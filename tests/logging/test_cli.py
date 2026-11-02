#!/usr/bin/env python3
"""Exercise standard levels, selection and output at the executable boundary."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--binary", type=Path, default=root / "_build/default/backend/driver/main.exe")
parser.add_argument("--runtime", type=Path, default=root / "_build/install/default")
args = parser.parse_args()

with tempfile.TemporaryDirectory(prefix="cerberus-logging-") as temp:
    directory = Path(temp)
    source = directory / "input.c"
    source.write_text("int f(int x) { return x + 1; }\nint main(void) { return f(3); }\n")

    def run(*options, success=True, with_input=True):
        result = subprocess.run(
            [str(args.binary.resolve()), "--runtime", str(args.runtime.resolve()),
             "--nolibc", *options, *([str(source)] if with_input else [])],
            capture_output=True, text=True, cwd=directory, timeout=30)
        assert (result.returncode == 0) == success, result.stderr
        return result

    def events(text):
        return [json.loads(line) for line in text.splitlines()]

    baseline = run()
    assert baseline.stdout == baseline.stderr == ""
    listed = run("--list-debug-sources")
    assert listed.stderr == ""
    names = listed.stdout.splitlines()
    assert names == sorted(set(names))
    assert "Pipeline.cpp" in names
    assert "Pipeline.c_frontend" in names
    assert "Pipeline.core_frontend" not in names
    assert "Pipeline.pass_message" in names
    assert not any(name in names for name in
                   ("Main.cerberus", "Main_vip.cerberus", "Main_cheri_coq.cerberus",
                    "Cerb_diagnostic.warn", "Milicore_label_inline.inline_label"))
    assert "Cabs_to_ail.desugar_expression0" in names
    assert "Core_reduction.one_step_unseq_aux" not in names
    assert "Translation.floating_conversion_TODO" not in names
    assert "Formatted.convert" not in names
    assert run("--list-debug-sources", "-q").stdout.splitlines() == names
    assert run("--list-debug-sources", "--debug=Missing.no_such_function").stdout.splitlines() == names
    assert run("--list-debug-sources", "-q").stderr == ""
    selector = "--debug=Cabs_to_ail.desugar_expression0"
    for destination in ("stdout", "stderr"):
        result = run(selector, "--debug-format=json", "--debug-output=" + destination)
        rows = events(getattr(result, destination))
        assert rows and all(row["source"] == "Cabs_to_ail.desugar_expression0" for row in rows)
        assert all(row["schema_version"] == 1 and "verbosity" not in row for row in rows)
        assert getattr(result, "stderr" if destination == "stdout" else "stdout") == ""

    rows = events(run("--debug=Cabs_to_ail", "--debug=Cabs_to_ail_effect", "--debug-format=json").stderr)
    assert {row["module"] for row in rows} == {"Cabs_to_ail", "Cabs_to_ail_effect"}
    # Native OCaml functions use the same automatic selection as Lem exports.
    rows = events(run("--debug=Pipeline.cpp", "--debug-format=json").stderr)
    assert rows and all(r["source"] == "Pipeline.cpp" for r in rows)
    assert rows[0]["message"] == "C preprocessor"
    rows = events(run("--debug=Pipeline", "--debug-format=json").stderr)
    assert {r["source"] for r in rows if r["level"] == "debug"} == {"Pipeline.cpp", "Pipeline.c_frontend"}
    assert all(r["module"] == "Pipeline" for r in rows)
    info = events(run("-v", "--debug-format=json").stderr)
    assert info and {r["level"] for r in info} == {"info"}
    assert {r["source"] for r in info} == {"Pipeline.pass_message"}
    selected_info = events(run("--verbosity=error", "--debug=Pipeline.pass_message",
                               "--debug-format=json").stderr)
    assert selected_info == info
    debug = events(run("-vv", "--debug-format=json").stderr)
    assert any(r["level"] == "debug" for r in debug)
    assert run("-vv", "--verbosity=warning").stderr == ""
    assert run(selector, "-vv", "-q").stderr == ""
    assert run("--debug=all", "--verbosity=quiet").stderr == ""
    # Selecting a source must not hide warnings from other sources.
    warning = run(selector, "--iso", "--switches=inner_arg_temps", "--debug-format=json")
    driver_warning = [r for r in events(warning.stderr)
                      if r["message"] == "the --iso argument overrides --switches"]
    assert len(driver_warning) == 1 and driver_warning[0]["level"] == "warning"
    driver_source = driver_warning[0]["source"]
    assert driver_source in ("Main.cerberus", "Main_vip.cerberus", "Main_cheri_coq.cerberus")
    warning_options = ("--iso", "--switches=inner_arg_temps", "--debug-format=json")
    assert run("--verbosity=error", *warning_options).stderr == ""
    assert events(run("--verbosity=error", "--debug=" + driver_source,
                      *warning_options).stderr) == driver_warning
    assert run("--quiet", "--debug=" + driver_source, *warning_options).stderr == ""
    assert driver_source in run("--list-debug-sources", "--quiet",
                                *warning_options).stdout.splitlines()

    # Logging policy must not change the requested program display.
    pretty = run("--pp=ail").stdout
    assert run("-vv", "--pp=ail").stdout == pretty
    assert run("--pp=ail", "--pp_flags=verbose").stdout != pretty

    logfile = directory / "stdout"
    options = (selector, "--debug-format=json", "--debug-output=file:" + str(logfile))
    assert run(*options).stderr == ""
    first_count = len(events(logfile.read_text()))
    assert first_count > 0
    assert run(*options).stdout == ""
    assert len(events(logfile.read_text())) == 2 * first_count
    assert "[debug] Cabs_to_ail.desugar_expression0:" in run(selector).stderr
    assert run("--debug=Missing.no_such_function").stderr == ""
    for invalid in ("file:cabs_to_ail.lem", "desugar_expression",
                    "Cabs_to_ail*", "Cabs_to_ail.desugar_?", "module:Cabs_to_ail",
                    "cabs_to_ail.desugar_expression", "Cabs_to_ail._"):
        assert "invalid debug selector" in run("--debug=" + invalid, success=False).stderr
    assert "debug-format" in run("--debug-format=bogus", success=False).stderr
    assert "debug output:" in run("--debug-output=" + str(directory / "missing/log"), success=False).stderr
    source.write_text("int main(void) { int x = 3; int *p = &x; *p += 1; return x - 4; }\n")
    execution_log = directory / "execution.jsonl"
    run("--exec", "--debug=Driver_ocaml", "--debug=Smt2.runND",
        "--debug=Impl_mem", "--debug=Impl_mem.Concrete", "--debug-format=json",
        "--debug-output=" + str(execution_log))
    rows = events(execution_log.read_text())
    sources = {r["source"] for r in rows}
    assert "Driver_ocaml.drive" in sources and "Smt2.runND" in sources
    assert "Impl_mem.Concrete.load" in sources or "Impl_mem.repr" in sources
    execution_names = run("--exec", "--list-debug-sources", "-q").stdout.splitlines()
    assert sources <= set(execution_names)
    # A real Lem warning uses its automatic function name and normal severity.
    source.write_text("int main(void) { switch (0) { case 2 ... 1: return 1; } return 0; }\n")
    warning_source = "Cabs_to_ail.desugar_statement_aux"
    warnings = events(run("--debug-format=json").stderr)
    assert any(r["source"] == warning_source and r["level"] == "warning" for r in warnings)
    assert run("--verbosity=error").stderr == ""
    selected_warning = events(run("--verbosity=error", "--debug=" + warning_source,
                                  "--debug-format=json").stderr)
    assert any(r["source"] == warning_source and r["level"] == "warning" for r in selected_warning)
    assert run("--debug=" + warning_source, "--quiet").stderr == ""
    assert run("--quiet", "--debug=" + warning_source).stderr == ""
    assert warning_source in run("--list-debug-sources", "--quiet").stdout.splitlines()
    source.write_text("int main(void) { return missing_identifier; }\n")
    failure = run("-q", success=False)
    assert failure.stderr  # Quiet logging cannot hide or swallow compiler errors.
    partial = run("--list-debug-sources", "-q", success=False)
    assert partial.stderr and "Pipeline.c_frontend" in partial.stdout.splitlines()
    assert not (directory / "cerb.prof").exists()
    assert not (directory / "cerb_times.csv").exists()
print("CLI logging tests passed")
