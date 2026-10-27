#!/usr/bin/env python3
"""Assemble the compact round-15 seed R2 source from accepted R1 text.

Earlier files are read only.  The local and shared outputs are byte-identical;
compilation is deliberately separate and uses AHP/round3/lean1.sh via bb heavy.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT / "AHP/round15/seed/r2"
base = (ROOT / "AHP/round15/seed/r1/Seed.lean").read_text()
new = (HERE / "R2Declarations.lean").read_text()
source = base.rstrip() + "\n" + new
local = HERE / "Leading.lean"
shared = ROOT / "AHP/round15/shared/seed/R2_Leading.lean"
local.write_text(source)
shared.parent.mkdir(parents=True, exist_ok=True)
shared.write_text(source)
record = {
    "base": "AHP/round15/seed/r1/Seed.lean",
    "fragment": "AHP/round15/seed/r2/R2Declarations.lean",
    "local": str(local.relative_to(ROOT)),
    "shared": str(shared.relative_to(ROOT)),
    "sha256": hashlib.sha256(source.encode()).hexdigest(),
    "lines": len(source.splitlines()),
    "identical": local.read_bytes() == shared.read_bytes(),
}
(HERE / "BUILD.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
