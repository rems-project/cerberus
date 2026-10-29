# Logging

Cerberus uses [Logs](https://erratique.ch/software/logs/doc/Logs/index.html#usage).
Configure logging once in the executable, before starting translation-unit workers.
Every translation unit shares that policy. Libraries emit messages; the shared
logging implementation manages automatic Debug sources. Libraries do not install
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
  during this run, even when their messages are disabled. No binary scan is used.
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
  Cerb_log_auto.debugf __FUNCTION__ (fun m -> m "input: %a" pp_input input);
  (* ... *)
```

Pass `__FUNCTION__` at each Debug call site. Both native OCaml and Lem-generated
calls use the shared Saturn cache; no Debug source registration is needed.
Place expensive computations inside the callback so disabled logging does not
perform them. `debugf` accepts the usual Logs formatting callback, including
`%a` printers, headers and tags. Info, Warning and Error messages use the ordinary
Logs API with explicit sources created once at module scope.

Lem uses a small, non-monadic adapter because its strings are not OCaml format
strings:

```ocaml
let translate input =
  let () = Debug.debug (fun () -> show input) in
  (* ... *)
```

Lem has no `__FUNCTION__` identifier, but its OCaml target replacement inserts
it at the call site. Both paths use the enclosing OCaml function name. The Dune
`Cerb_frontend__`, `Cerb_backend__` and `Dune__exe__` wrappers are removed, and
nested or anonymous functions use the outer function name. Numeric suffixes
remain significant: `fn0` and `fn` differ. For example, the native preprocessor
message is selected by `Pipeline.cpp`, or by `Pipeline` along with the module's
other functions.

`Debug.info`, `Debug.warn` and `Debug.err` still take an explicit source created
with `Debug.source`. `Debug.debug_located loc (fun () -> message)` formats the
location only when enabled. `Debug.debug_enabled ()` uses the same automatic name.
`Debug.debug_enabled` is only needed when deciding *whether* to emit a message
requires expensive work, as in symbol-description comparisons. It is not needed
for ordinary message construction.

There is no logging monad, context parameter, domain list, numeric verbosity or
compatibility API. No mutable logging configuration is stored in Lem state.
HOL, Isabelle and Coq receive a trivial source type and no-op logging functions;
they do not evaluate message callbacks. Error handling stays in the existing
error mechanisms.

## Reporter and concurrency

The reporter formats each record independently, outside its mutex. A mutex guards
the complete write and flush, and also closure. This prevents records from
interleaving across threads or OCaml 5 domains and allows a formatter to log a
nested message without deadlocking. It does not impose a deterministic order on
concurrent events. Close after workers join; writes after closure are errors.
The close function is idempotent and does not close borrowed stdout/stderr.

Configure the shared policy and reporter before workers start. Concurrent
reconfiguration or changing source levels is outside this contract. On first
use, Saturn caches the selection result for the static function-name address.
A writer mutex serializes cold registration, including source deduplication;
ordinary cache hits do not take that application mutex. Negative decisions use
`None`, positive decisions reuse a cached `Some src`. This allocates no option
wrapper on a hit. Sources registered after reporter creation acquire cached
text prefixes on their first event through an atomic immutable-map update.

The automatic API accepts native static strings, normally `__FUNCTION__`.
Active logging rejects moving heap strings with `Invalid_argument`; it has no
content-hash fallback. Two small C helpers hash the address and check the OCaml 5
out-of-heap string header. They do not scan binary data. Globally disabled calls
skip lookup and validation unless source discovery was requested. Entries grow with distinct encountered static
addresses, not the number of C functions, TUs, messages or repeated calls.
Multi-domain correctness is tested; parallel-TU throughput is not established.

JSON records contain `schema_version` (1), `source`, `module`, an optional
`function`, `level`, and `message`. Newlines and control characters are escaped.
Optional Logs tags supply `location` and `translation_unit`; arbitrary extra tags
appear under `tags`. No translation-unit context is threaded through elaboration
just to carry the shared policy. Add per-input metadata at a call site only when
needed.

## Display and profiling

Logging no longer changes pretty-printing or hides evaluated program output.
Use `--pp_flags=annot` for inferred Ail annotations, `--pp_flags=early` to display
Ail before typing and Core before rewriting, and `--pp_flags=verbose` for internal
symbol identities, provenance and extra display detail. Flags can be combined.
The existing `loc` flag remains available.

Unused numeric-level timing hooks and their implicit `cerb.prof`/`cerb_times.csv`
files have been removed. Profiling should be configured independently of logging.
This does not change separate tracing facilities or the BMC/web backends' own
backend-specific diagnostics.

## Validation

Requires native OCaml >= 5.2 and < 6, Logs >= 0.10 (including `logs.cli`),
and Saturn >= 1.0 and < 2. The static-header check must be reviewed for a new
OCaml major runtime. Bytecode automatic Debug names are not supported.
Regenerate Lem output when building:

```sh
make -j8
dune runtest tests/logging
python3 tests/logging/test_cli.py
python3 tests/logging/test_provers.py
tests/run-ci.sh
```

The prover test checks generation and erasure in all three targets; it does not
claim to compile Cerberus' complete prover developments. Domain and systhread tests run on OCaml 5. See `LOGGING_PERFORMANCE.md` for measured
costs and the limits of comparisons with the old numeric policy.
