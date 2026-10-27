#!/usr/bin/env python3
"""Read-only source/log checks; writes only this pin's audit.json. No numerics."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PIN = HERE / "Statement.lean"
src = PIN.read_text()
s1path = ROOT / "AHP/round2/s1-touching/pin/Statement.lean"
s2path = ROOT / "AHP/round2/s2-nonvacuity/pin/Statement.lean"
s1 = s1path.read_text()
s2 = s2path.read_text()


def block(text, name):
    match = re.search(r"^def " + re.escape(name) + r"\b[^\n]*(?:\n[^\n]+)*", text, re.M)
    assert match, name
    return match.group(0)


copies = {}
for name in ["TouchBond", "CoversPlaqFour", "CurlReadsTouch", "PerCubeRegularTouch", "ClassCoupledFour"]:
    assert block(src, name) == block(s2, name), name
    copies[name] = str(s2path.relative_to(ROOT))
for name in ["plaqCorner", "selCorner"]:
    assert block(src, name) == block(s1, name), name
    copies[name] = str(s1path.relative_to(ROOT))
expected = block(s1, "P428TouchConsistent").replace("P428TouchConsistent", "P428TouchFour").replace("ClassCoupledCorner", "ClassCoupledFour")
assert block(src, "P428TouchFour") == expected
assert block(src, "GoalPos1") == "def GoalPos1 : Prop := P428TouchFour"
assert block(src, "GoalNeg1") == "def GoalNeg1 : Prop := ¬ GoalPos1"
assert "variable {L : PeriodicLatticeExtent}" in src
assert "set_option autoImplicit false" in src
imports = re.findall(r"^import (\S+)$", src, re.M)
assert imports == ["D1Lit"]
for mod in imports:
    assert (ROOT / "lean/src" / (mod.replace(".", "/") + ".lean")).is_file()
forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b", src)
assert not forbidden, forbidden
assert (HERE / "Statement.lean.exit").read_text().strip() == "0"
log = (HERE / "Statement.lean.log").read_text()
assert not re.search(r"\b(?:error|warning):", log)
records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
allowed = {"propext", "Classical.choice", "Quot.sound"}
names = re.findall(r"^def (\w+)\b", src, re.M)
assert len(records) == len(names) == 10
assert {name for name, _ in records} == {"Round3.S1Proper." + name for name in names}
for name, deps in records:
    assert {d.strip() for d in deps.split(",") if d.strip()} <= allowed, name
checks = re.findall(r"^#check (\w+)$", src, re.M)
assert checks == names


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


result = {
    "status": "pin-compiled-goals-unproved",
    "namespace": "Round3.S1Proper",
    "source_sha256": sha(PIN),
    "log_sha256": sha(HERE / "Statement.lean.log"),
    "exit": 0,
    "local_definitions": len(names),
    "check_lines": len(checks),
    "permitted_axiom_records": len(records),
    "warnings": 0,
    "forbidden_token_hits": forbidden,
    "imports": imports,
    "verbatim_copies": copies,
    "headline_matches_round2_except_name_and_class": True,
    "negative_is_exact_negation": True,
    "declaration_lines": {name: next(i for i, line in enumerate(src.splitlines(), 1) if line.startswith("def " + name + " ")) for name in names},
}
(HERE / "audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
