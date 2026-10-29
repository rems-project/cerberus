#!/usr/bin/env python3
"""Check Lem's actual HOL, Isabelle and Coq output for the logging facade.

This checks generation and erasure, not the surrounding Cerberus proofs.
Run under the same opam switch used to build Cerberus.
"""
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory(prefix="cerberus-provers-") as tmp:
    subprocess.run(["lem", "-wl", "ign", "-lib", "frontend/model", "-lib",
                    "frontend/model/ail", "-lib", "frontend/concurrency",
                    "-outdir", tmp, "-hol", "-isa", "-coq", "frontend/model/debug.lem"],
                   cwd=root, check=True)
    outputs = {name: (Path(tmp) / name).read_text()
               for name in ("debugScript.sml", "Debug.thy", "debug.v")}
    for name, text in outputs.items():
        assert "Cerb_log" not in text and "Logs." not in text, name
        assert "logM" not in text and "warnM" not in text, name
    coq = outputs["debug.v"]
    assert "Inductive src" in coq and "Definition source " in coq
    assert re.search(r"Definition debug_enabled\b[^.]+:=\s*false\.", coq)
    for operation in ("debug", "info", "warn", "err", "debug_located"):
        assert re.search(r"Definition " + operation + r"\b[^.]+:=\s*tt\.", coq), operation
print("HOL, Isabelle and Coq logging erasure checks passed")
