#!/usr/bin/env python3
"""Check that explicit display flags are independent of logging verbosity."""
import argparse
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--binary", type=Path, default=root / "_build/default/backend/driver/main.exe")
parser.add_argument("--runtime", type=Path, default=root / "_build/install/default")
args = parser.parse_args()

with tempfile.TemporaryDirectory(prefix="cerberus-display-") as temp:
    source = Path(temp) / "input.c"
    source.write_text("int f(int x) { return x + 1; }\nint main(void) { return f(3); }\n")

    def run(*options):
        return subprocess.run(
            [str(args.binary.resolve()), "--runtime", str(args.runtime.resolve()),
             "--nolibc", *options, str(source)], cwd=temp,
            capture_output=True, text=True, timeout=30, check=True).stdout

    for language in ("ail", "core"):
        for flags in ((), ("--pp_flags=early",), ("--pp_flags=verbose",),
                      ("--pp_flags=annot",)):
            options = ("--pp=" + language, *flags)
            assert run(*options) == run("-d6", *options), options
    plain = run("--pp=ail")
    assert run("--pp=ail", "--pp_flags=verbose") != plain
    assert run("--pp=ail", "--pp_flags=annot") != plain
    assert run("--ast=ail", "--pp_flags=early") != run("--ast=ail")
    assert "BEGIN (before Core rewrite)" in run("--rewrite", "--ast=core", "--pp_flags=early")
    assert "BEGIN (before Core rewrite)" not in run("--rewrite", "--ast=core")
print("Display flags are independent of logging verbosity")
