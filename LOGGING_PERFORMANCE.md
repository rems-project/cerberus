# Logging performance

Measured 2026-10-29 with native OCaml 5.2.1, Logs 0.10.0 and Saturn 1.0.0, on a Linux amd64 development host. Release builds were pinned to one allowed CPU. The numeric baseline is `ae70925fc`, still the upstream master head when checked. The pre-registered Logs version is the previous PR head `de9683d32`. The Saturn column measures the implementation in this PR, including cached options and the corrected late-source prefix cache.

The measured production sources match commit `ff948c3dc`; the following commit adds documentation and benchmark tooling.

## Fresh command-line invocations

Each sample starts a new process and includes startup, preprocessing, TU processing and exit. There are 20 balanced rounds per case; text output goes to `/dev/null`, so formatting, synchronization and writes still execute. No builds, tests or analysis ran concurrently. Source listing is not requested. The compiler processes each TU with `--nolibc`, without executing the C program.

The broad profile in `tests/logging/level2-profile.json` selects similar call sites to the numeric baseline's `-d2`. It is not identical to the numeric event set. Ordered JSON records agree between the pre-registered version, Saturn and Fixed on string, vfscanf and the generated input after normalizing the old `desugar_expression` label to the extracted `desugar_expression0` name.

All percentages use the same row's master median as 100%; lower is faster. The Fixed column is the preserved filtered-scan experiment, not a selectable backend in this PR.

| Input / policy | Master ms | Pre-registered | Saturn | Fixed experiment |
|---|---:|---:|---:|---:|
| libc string | 62.68 | 102.6% | 100.9% | 106.3% |
| libc vfscanf | 72.63 | 104.1% | 102.9% | 108.5% |
| grep | 71.44 | 102.8% | 103.4% | 106.7% |
| Chacha20 | 64.85 | 103.4% | 102.5% | 107.3% |
| 256 generated functions | 166.01 | 105.4% | 107.7% | 107.1% |
| string ×40 | 1316.53 | 106.6% | 110.9% | 106.8% |
| vfscanf ×28 | 801.98 | 109.4% | 114.1% | 110.2% |
| 256 functions, unmatched selector | 130.39 | 99.5% | 100.6% | 101.8% |
| 256 functions, logging off | 130.01 | 99.2% | 98.8% | 99.2% |

The first seven rows enable the broad profile. On the unmatched-selector row, the new implementations perform decisions but emit no Debug messages; master has logging off. The last row has logging off everywhere. The two large inputs repeat existing libc function bodies with renamed definitions, reaching 707,163 and 708,240 decisions; they are scaling inputs, not independent large applications.

Saturn takes 100.9–114.1% of master time on the enabled rows. Its logging-off result is consistent with equality: the median paired change is −0.6%, with a nominal 95% bootstrap interval of [−2.0%, +0.4%]. Enabled logging still has measurable overhead; this does not establish the absence of a material slowdown on every workload.

Fixed takes about 3.8–5.7% longer than Saturn on the four smaller real inputs. On string ×40 and vfscanf ×28, it is 3.7% and 3.5% faster in paired comparisons, with intervals [−4.4%, −2.7%] and [−4.1%, −2.1%]. This final run resolves a large-input advantage that earlier runs did not. The chosen Saturn design favors automatic call-site ergonomics and simpler maintenance; it is not universally fastest.

Intervals resample paired rounds 10,000 times and describe the median paired percentage change, which can differ from the ratio of medians in the table. They are exploratory per-case intervals without a multiple-comparison correction; they do not account for every source of host variability. Multi-domain correctness is tested, but parallel-TU throughput is unmeasured.

## Decision cost and allocation

Warm `debug_enabled` lookup medians from six fresh processes, each with three million warmup and three million measured queries. These include loop/array selection; no message construction or output occurs. Names are native static literals.

| Addresses cycled | Rejected ns | Enabled ns |
|---|---:|---:|
| 1 | 12.09 | 12.10 |
| 16 | 14.47 | 13.96 |
| 128 | 16.87 | 16.23 |
| 4,096 | 30.53 | 29.00 |

Maximum measured warm allocation was 96 bytes over three million decisions: constant measurement overhead, not a wrapper per hit. Saturn `find_exn` returns the cached `Logs.src option` itself. `None` is immediate; `Some src` costs 16 bytes once per enabled pointer on this runtime. A dummy source would save that admission allocation while introducing a sentinel invariant. Ordinary caller closures and enabled reporter work are separate costs.

The final microbenchmark with changing integer messages measures the following medians of five samples (20 million disabled calls or 100,000 emitted messages per sample):

| Path | ns/call | allocated bytes/call |
|---|---:|---:|
| old integer gate | 2.092 | 32.000 |
| native Logs | 3.456 | 48.000 |
| Lem adapter | 2.261 | 32.000 |
| old enabled text | 478.542 | 47.201 |
| enabled text | 590.358 | 704.001 |
| enabled JSON | 1337.452 | 2152.000 |

The old-style gate/printer are synthetic controls, not a second full Cerberus invocation. Their prefixes differ from the new reporter, which emits a qualified source and synchronizes complete records. Enabled JSON provides structured fields at additional formatting/allocation cost. The globally inactive Lem path retains the caller closure but performs no pointer lookup.

## Retained cache memory

Five fresh processes per size; median full-GC live-heap growth above an already configured empty policy. These generated names each have a distinct static address. Negative entries allocate no Logs sources. Positive growth includes canonical names, the source registry, Logs sources and cached options. Both columns exclude the empty policy/table, static literal storage, reporter prefixes and the rest of process RSS.

| Distinct addresses | All negative KiB | All positive KiB |
|---|---:|---:|
| 41 | 2.14 | 8.88 |
| 50 | 2.45 | 10.63 |
| 256 | 15.23 | 58.98 |
| 1,024 | 61.01 | 236.78 |
| 4,096 | 189.88 | 893.65 |
| 16,384 | 977.90 | 3793.10 |

The sampled real frontend traces encounter roughly 41–50 addresses, even in the large runs. Repeated TUs reuse the same entries; adding logging call sites drives growth. The table above sizes synthetic names, not the exact positive/negative mixture or name lengths in those traces. A bounded cache is possible, but eviction introduces shared bookkeeping and does not itself release sources retained by Logs.

## Reproduce

Build each checkout with the same compiler/dependencies using `make PROFILE=release` so Lem output is regenerated. Run without concurrent builds or tests. Choose an allowed CPU for `--cpu` if pinning is desired. Each frontend sample is a fresh process; preliminary runs warm filesystem caches, not a persistent logging table.

```sh
dune exec --profile release tests/logging/bench_lookup.exe -- memory 1024 negative
dune exec --profile release tests/logging/bench_lookup.exe -- micro 128 positive
dune exec --profile release tests/logging/bench_logging.exe
python3 tests/logging/bench_frontend.py /path/to/master /path/to/saturn \
  --runs 20 --functions 256
python3 tests/logging/bench_frontend.py /path/to/master /path/to/saturn \
  --runs 20 --input runtime/libc/src/string.c --logging \
  --baseline-arg=-d2 --candidate-args-file=tests/logging/level2-profile.json
```

The frontend runner records samples, run orders, command lines, revisions, dirty status and executable SHA-256 hashes. Dirty HEAD alone does not identify a tested implementation. The broader development comparison also preserves raw samples and hashes for the experimental variants; those variants and binary scans are not included in the production API.
