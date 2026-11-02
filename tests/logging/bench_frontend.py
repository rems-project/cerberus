#!/usr/bin/env python3
"""Compare built checkouts with a fresh process for every frontend sample."""
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("baseline", type=Path)
parser.add_argument("candidate", type=Path)
parser.add_argument("--previous", type=Path, help="Include an earlier implementation in the same run")
parser.add_argument("--runs", type=int, default=15)
parser.add_argument("--functions", type=int, default=200)
parser.add_argument("--input", type=Path, help="Use an existing C file instead of generated functions")
parser.add_argument("--cpu", type=int, help="Pin samples to an allowed CPU (Linux)")
parser.add_argument("--baseline-arg", action="append", default=[])
parser.add_argument("--candidate-arg", action="append", default=[])
parser.add_argument("--previous-arg", action="append", default=[])
for version in ("baseline", "candidate", "previous"):
    parser.add_argument("--" + version + "-args-file", type=Path,
                        help="JSON array of additional arguments for this checkout")
parser.add_argument("--logging", action="store_true", help="Allow and discard stderr log output")
args = parser.parse_args()
if args.runs < 1 or args.functions < 1:
    parser.error("runs and functions must be positive")
if args.cpu is not None:
    os.sched_setaffinity(0, {args.cpu})
for version in ("baseline", "candidate", "previous"):
    path = getattr(args, version + "_args_file")
    if path is not None:
        extra = json.loads(path.read_text())
        if not isinstance(extra, list) or not all(isinstance(x, str) for x in extra):
            parser.error(str(path) + " must contain an array of strings")
        getattr(args, version + "_arg").extend(extra)
environment = {k: v for k, v in os.environ.items() if not k.startswith("CERB_LOG_")}

with tempfile.TemporaryDirectory(prefix="cerberus-bench-") as temp:
    source = args.input.resolve() if args.input else Path(temp) / "input.c"
    if args.input is None:
        source.write_text("\n".join(
            f"int f{i}(int x) {{ int a[4] = {{x, 1, 2, 3}}; "
            "for (int j = 0; j < 4; ++j) x += a[j]; return x; }"
            for i in range(args.functions)))
    versions = [("baseline", args.baseline)]
    if args.previous is not None:
        versions.append(("previous", args.previous))
    versions.append(("candidate", args.candidate))
    commands = {name: [str(root.resolve() / "_build/default/backend/driver/main.exe"),
                       "--runtime", str(root.resolve() / "_build/install/default"),
                       "--nolibc", *getattr(args, name + "_arg"), str(source)]
                for name, root in versions}

    def run(name):
        start = time.perf_counter()
        result = subprocess.run(commands[name], stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL if args.logging else subprocess.PIPE,
                                cwd=temp, env=environment)
        elapsed = time.perf_counter() - start
        assert result.returncode == 0, result.stderr
        assert result.stdout == b"", result.stdout
        if not args.logging:
            assert result.stderr == b"", result.stderr
        return elapsed

    for _ in range(3):
        for name in commands:
            run(name)
    results = {name: [] for name in commands}
    orders = list(itertools.permutations(commands))
    for i in range(args.runs):
        for name in orders[i % len(orders)]:
            results[name].append(run(name))
    medians = {name: statistics.median(values) for name, values in results.items()}
    revisions = {name: subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        for name, root in versions}
    binaries = {name: hashlib.sha256((root.resolve() / "_build/default/backend/driver/main.exe").read_bytes()).hexdigest()
                for name, root in versions}
    dirty = {name: bool(subprocess.check_output(["git", "-C", str(root), "status", "--porcelain"]))
             for name, root in versions}
    print(json.dumps({"functions": args.functions if args.input is None else None,
                      "input": str(args.input) if args.input else None,
                      "cpu": args.cpu, "fresh_process_every_sample": True,
                      "runs": args.runs, "logging": args.logging, "commands": commands,
                      "revisions": revisions, "binary_sha256": binaries, "dirty": dirty, "run_orders": orders,
                      "seconds": results, "median_seconds": medians,
                      "candidate_over_baseline": medians["candidate"] / medians["baseline"]}, indent=2))
