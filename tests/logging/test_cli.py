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
    assert "Pipeline" in names
    assert "Cabs_to_ail.desugar_expression0" in names
    assert "Core_reduction.one_step_unseq_aux" not in names
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
    info = events(run("-v", "--debug-format=json").stderr)
    assert info and {r["level"] for r in info} == {"info"}
    debug = events(run("-vv", "--debug-format=json").stderr)
    assert any(r["level"] == "debug" for r in debug)
    assert run("-vv", "--verbosity=warning").stderr == ""
    assert run(selector, "-vv", "-q").stderr == ""
    assert run("--debug=all", "--verbosity=quiet").stderr == ""
    # Selecting a source must not hide warnings from other sources.
    warning = run(selector, "--iso", "--switches=inner_arg_temps", "--debug-format=json")
    assert any(r["level"] == "warning" and r["source"] == "Main.cerberus" for r in events(warning.stderr))

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
    source.write_text("int main(void) { return missing_identifier; }\n")
    failure = run("-q", success=False)
    assert failure.stderr  # Quiet logging cannot hide or swallow compiler errors.
    partial = run("--list-debug-sources", "-q", success=False)
    assert partial.stderr and "Pipeline" in partial.stdout.splitlines()
    assert not (directory / "cerb.prof").exists()
    assert not (directory / "cerb_times.csv").exists()
print("CLI logging tests passed")
