# Logging performance and design choices

The final logging implementation is the one developed in [#1027](https://github.com/rems-project/cerberus/pull/1027), rebuilt as a reviewable series on master `1fcfb570b`. That PR retains the earlier pre-registration, Fixed-scan and domain-local-cache experiments. Their timings describe the revisions measured there, not current master or this rebuilt series.

## Effect of the cache commit

Measured on 2 November 2026 with native OCaml 5.2.1, Logs 0.10.0 and Saturn 1.0.0 on Linux amd64. Release binaries were pinned to one allowed CPU, with no builds or tests running during measurement. Both binaries use the same upstream base and public API.

The baseline is the preceding concurrency commit, `8111fbf25`: it resolves names and selectors by string contents on each call and formats each message through `Format`. The candidate adds the address cache, indexed name normalization, cached text prefixes and the plain-string formatting fast path. This measures those optimizations together. It is **not** a comparison against numeric-level master, Fixed, or the previous PR head.

Each frontend sample starts a fresh process and includes startup, preprocessing, translation and exit. There are 16 paired rounds, alternating order after three warmup rounds. Text is written to `/dev/null`; formatting and writes execute, terminal rendering does not. Enabled rows use `tests/logging/level2-profile.json`. The generated input contains 256 small functions with array initialization and a loop. Percentages take the uncached median as 100%; lower is faster.

| Input / policy | Uncached ms | Cached ms | Cached / uncached |
|---|---:|---:|---:|
| libc string / enabled | 85.45 | 74.77 | 87.5% |
| libc vfscanf / enabled | 108.33 | 85.76 | 79.2% |
| 256 functions / enabled | 271.44 | 191.00 | 70.4% |
| 256 functions / unmatched selector | 178.53 | 140.87 | 78.9% |
| 256 functions / logging off | 137.23 | 138.84 | 101.2% |

Ordered JSON records agree between the binaries in all five cases. The logging-off paired median change is +1.1% (exploratory 95% bootstrap interval -2.4% to +3.8%). Whole-binary timing includes layout and host effects; this short run does not establish a general difference of about 1%. Both implementations already skip source lookup when Debug is globally inactive.

## Lookup and memory

The warm lookup benchmark calls the native API with a no-op reporter. Timings include the loop, array indexing, and Logs dispatch for accepted calls, but no message formatting or output. Each number is the median of five fresh processes, with three million calls after warmup. These are calls through the API, not the older decision-only measurements in #1027.

| Addresses | Policy | Uncached ns/call | Cached ns/call |
|---:|---|---:|---:|
| 128 | off | 3.06 | 3.05 |
| 128 | negative | 331.46 | 17.67 |
| 128 | positive | 419.40 | 37.55 |
| 128 | mixed | 393.31 | 27.43 |
| 4,096 | off | 3.07 | 3.04 |
| 4,096 | negative | 366.12 | 33.53 |
| 4,096 | positive | 488.20 | 47.17 |
| 4,096 | mixed | 466.74 | 36.88 |

“Negative” is an unmatched Debug call; “positive” is selected Debug. “Mixed” alternates rejected Debug, accepted Warning and accepted Error at each address. Cached off/negative calls allocate no memory per call. Positive native calls allocate 56 bytes in Logs dispatch; the cache adds no option or record allocation on hits. The correctness tests compare allocation with direct Logs calls.

Retained live-heap increases below are medians of five fresh processes after full GC, above an empty configured policy. Names are already canonical static literals. These figures include populated tables and any registered sources, but exclude static literals, reporter state, and extra strings needed to normalize wrapped names. The counts are synthetic working sets, not counts from the frontend runs.

| Addresses | Negative KiB | Positive KiB | Mixed KiB |
|---:|---:|---:|---:|
| 50 | 3.74 | 10.19 | 10.18 |
| 16,384 | 1489.62 | 3664.81 | 3663.63 |

Entries grow with distinct static logging addresses reached by the OCaml program, not with the number of input C functions, translation units or messages. Bounded eviction is possible, but would add bookkeeping and potentially contention. The current implementation favors simple lookup and predictable source identity.

## Alternatives and limits

- Pre-registered sources make lookup cheap but require declarations at call sites. Automatic `__FUNCTION__` sources remove that maintenance burden.
- The Fixed experiment scans native data and precomputes immutable address mappings, choosing among range, bitmap and hash layouts. It can win on sufficiently large traces, but adds C scanning, startup work and layout policies. The new measurements above do not update its crossover estimates.
- Small per-domain linear caches with CLOCK or RRIP eviction did not make the earlier whole-program runs faster: domain-local storage access, search and bookkeeping outweighed their lookup savings.
- Cached options keep “no source registered yet” explicit. A dummy source saves a small admission allocation but introduces a sentinel invariant; neither representation needs an option allocation on warm hits.

Concurrency correctness is tested on OCaml 5.2.1 domains and on systhreads in both 4.14.1 and 5.2.1. Parallel-TU throughput and contention remain unmeasured; Fixed's immutability could prove useful there. The timings above are for 5.2.1 only.

## Reproduction

Build the concurrency commit and this commit in separate worktrees with the same compiler and release profile. Regenerate Lem before building. The current benchmark can compare those worktrees with a fresh process per sample:

```sh
python3 tests/logging/bench_frontend.py ../before-cache . --runs=16 --functions=256 \
  --baseline-args-file=tests/logging/level2-profile.json \
  --candidate-args-file=tests/logging/level2-profile.json --logging --cpu=0
dune build --profile=release tests/logging/bench_lookup.exe
_build/default/tests/logging/bench_lookup.exe micro 128 negative
_build/default/tests/logging/bench_lookup.exe memory 16384 negative
```

Choose an allowed CPU for the host. Use `--input=runtime/libc/src/string.c` or `vfscanf.c` for the real-file cases. Raw samples, binary hashes and exact commands from this run are retained in the session artifact `artifacts/logging-clean-series/measurements.json`.
