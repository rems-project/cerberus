# Logging

Cerberus uses [Logs](https://erratique.ch/software/logs/doc/Logs/index.html#usage).
Configure logging once in the executable, before workers start. Every translation unit shares that policy. Libraries emit messages; the shared
logging implementation manages automatic sources. Libraries do not install
reporters or change levels.

## Command line

The default threshold is Warning. The standard Logs CLI options apply:

- `-v` or `--verbose`: Info; `-vv`: Debug for all sources.
- `--verbosity=quiet|error|warning|info|debug`: explicit threshold, overriding `-v`.
- `-q` or `--quiet`: suppress logging, overriding verbosity and source selection.
- `--debug=Module` or `--debug=Module.function`: enable Debug for those sources.
  Repeat the option to select several sources; `--debug=all` selects everything.
  Unselected sources keep the usual threshold, including their warnings.
- `--list-debug-sources`: process the input, then print source names to stdout
  at exit. Includes explicitly registered sources and automatic names encountered
  during this run, even when their messages are disabled.
- `--debug-output=stderr|stdout|PATH`: destination (default stderr). Files are
  appended. Use `file:PATH` when a filename would otherwise mean stdout/stderr.
- `--debug-format=text|json`: text (default) or one JSON object per record.

For example:

```sh
cerberus --list-debug-sources input.c
cerberus --debug=Cabs_to_ail.desugar_expression0 input.c
cerberus --debug=Cabs_to_ail --debug=Cabs_to_ail_effect \
  --debug-format=json --debug-output=elaboration.jsonl input.c
```

Names are exact and case-sensitive. Module components start with an uppercase
letter; a function starts with a lowercase letter or underscore and must be
qualified. `Outer.Inner` selects that module, not all of `Outer`; use
`Outer.Inner.parse` for just that function. Selectors are checked for valid syntax. Unknown names are accepted because an
automatic source may not have been called yet; a typo can therefore select
nothing. Filenames, globs, unqualified functions and numeric levels are not supported.

Source listing depends on the input and the paths taken. Unvisited automatic
sites, including calls inside unevaluated callbacks, are absent. Explicitly
registered sources are listed regardless of whether they were reached. Listing
requests discovery even with `--quiet`; it adds lookup work but does not enable
messages or evaluate disabled message callbacks. Ordinary inactive logging skips
that work. On a normal error exit the list contains discoveries made before the
error; the command still fails. The list shares stdout with any requested program
output, so omit pretty-printing or execution output when collecting names.

Compiler errors and program output remain independent of logging. Quiet logging
cannot turn a failed compilation into a success. Choosing stdout for logs shares
that stream with normal program output; use a file for a separate JSON stream.

## Writing messages

Use Debug for internal stages and implementation notes, Info for progress,
Warning for recoverable problems, and Error for failures worth reporting.
Return or raise the actual error separately. Libraries should not use App or the
default source. Follow Logs' lazy message convention in OCaml:

```ocaml
let translate input =
  Cerb_log.debug __FUNCTION__ (fun m -> m "input: %a" pp_input input);
  (* ... *)
```

Pass `__FUNCTION__` to `Cerb_log.debug`, `Cerb_log.info`, `Cerb_log.warn` and `Cerb_log.err`.
Both native OCaml and Lem-generated calls resolve their sources automatically;
no source declaration is needed. Place expensive computations inside the callback
so disabled logging does not perform them. All four accept the usual Logs
formatting callback, including `%a` printers, headers and tags.

Lem uses a small, non-monadic adapter because its strings are not OCaml format
strings:

```ocaml
let translate input =
  let () = Debug.debug (fun m -> m (show input)) in
  (* ... *)
```

Lem has no `__FUNCTION__` identifier, but its OCaml target replacement inserts
it at the call site. Both paths use the enclosing OCaml function name. The Dune
`Cerb_frontend__`, `Cerb_backend__` and `Dune__exe__` wrappers are removed, and
nested or anonymous functions use the outer function name. Numeric suffixes
remain significant: `fn0` and `fn` differ. For example, the native preprocessor
message is selected by `Pipeline.cpp`, or by `Pipeline` along with the module's
other functions.

`Debug.warn (fun m -> m message)` and `Debug.err (fun m -> m message)`
use the same automatic function names. There is no Lem source declaration or
`Debug.info` adapter. Their OCaml exports use `Cerb_log.debug_string`,
`warn_string` and `err_string`. `Debug.debug_located loc (fun m -> m message)`
uses `debug_located_string` and formats the location only when a message is
emitted. Callbacks can emit zero or several messages. Put diagnostic-only
conditions inside the callback too, for example:

```ocaml
Debug.debug (fun m -> if sd1 <> sd2 then m "suspicious equality" else ())
```

There is no separate enabled-query function. Use the emitter only during its
callback; each emission is a complete Logs call with its own reporter
continuations. The callback itself runs only when its severity is enabled.

There is no logging monad, context parameter, domain list, numeric verbosity or
compatibility API. No mutable logging configuration is stored in Lem state.
HOL, Isabelle and Coq receive no-op logging functions;
they do not evaluate message callbacks. Error handling stays in the existing
error mechanisms.

## Reporter and concurrency

Configure the policy and reporter before workers start; reconfiguration is
allowed after they have joined. Source levels and selectors stay fixed during
logging. Saturn registries support concurrent lookup. A mutex protects source
creation, with a second lookup inside the lock so aliases share one source.
Rejected calls register no source and take no source-creation lock.

The reporter formats each record outside its output mutex. The mutex guards
the complete write and flush, and also closure. Formatting can itself log
without deadlocking. Records do not interleave, but their order is not
deterministic. Close after workers join; writes after closure are errors.
Closing is idempotent and leaves borrowed stdout/stderr open. OCaml 4.14 uses
real systhreads mutexes with a small backport of `Mutex.protect`.


JSON records contain `schema_version` (1), `source`, `module`, an optional
`function`, `level`, and `message`. Newlines and control characters are escaped.
The optional `location` tag supplies source location metadata; arbitrary extra
tags appear under `tags`. No translation-unit context is threaded through
elaboration just to carry the shared policy.

## Display and profiling

Logging no longer changes pretty-printing or hides evaluated program output.
Use `--pp_flags=annot` for inferred Ail annotations, `--pp_flags=early` to display
Ail before typing and Core before rewriting, and `--pp_flags=verbose` for internal
symbol identities, provenance and extra display detail. Flags can be combined.
The existing `loc` flag remains available.

Unused numeric-level timing hooks and their implicit `cerb.prof`/`cerb_times.csv`
files have been removed. Profiling is independent of logging.

## Validation

Build with OCaml 4.14.1 or later in the 4.14 series, or >= 5.2 and < 6;
Logs >= 0.10, including `logs.cli`; and Saturn >= 1.0 and < 2.
Saturn does not support OCaml 5.0 or 5.1.
Regenerate Lem output before building:

```sh
make prelude-src
dune build --profile=release cerberus-lib.install cerberus.install
dune runtest --profile=release tests/logging
python3 tests/test_display.py
python3 tests/logging/test_cli.py
python3 tests/logging/test_provers.py
```

The prover test checks generation and erasure in HOL, Isabelle and Coq; it does
not compile Cerberus' complete prover developments. CI runs these tests and the
existing C and byte regressions on OCaml 4.14.1 and 5.2.1.

Systhread tests run on both compilers; OCaml 5 also runs real domain tests.
Parallel-TU throughput and contention remain unmeasured.
