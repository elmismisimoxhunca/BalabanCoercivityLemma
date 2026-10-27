#!/usr/bin/env python3
"""Source/log checks only; no numerical model and no Lean execution."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
pin = here.parent / "pin" / "Statement.lean"
attempt = here / "Attempt.lean"
source = attempt.read_text()
original = pin.read_text()
log = attempt.with_suffix(".lean.log").read_text()
exit_code = int(attempt.with_suffix(".lean.exit").read_text())
names = [
    "TouchBond", "CoversPlaqFour", "plaqCorner", "CoversPlaqCorner",
    "CurlReadsTouch", "PerCubeRegularTouch", "ClassCoupledFour",
    "ClassCoupledCorner", "ProperFourAt", "ProperCornerAt",
    "GoalPos1", "GoalNeg1", "GoalPos2", "GoalNeg2",
]

def declaration(text, name):
    match = re.search(r"^def " + re.escape(name) + r"\b", text, re.M)
    assert match, name
    return text[match.start():].split("\n\n", 1)[0]

matching = {name: declaration(source, name) == declaration(original, name)
            for name in names}
assert all(matching.values()), matching
imports = re.findall(r"^import (\S+)$", source, re.M)
assert imports == ["ZT5A", "D1Final", "ZR8Class"], imports
forbidden = re.findall(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b",
    source,
)
assert not forbidden, forbidden
assert exit_code == 0, exit_code
assert not re.search(r"\b(?:error|warning):", log)
records = re.findall(
    r"^'(.*)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    log, re.M,
)
allowed = {"propext", "Classical.choice", "Quot.sound"}
axioms = {name: [x.strip() for x in values.split(",") if x.strip()]
          for name, values in records}
assert all(set(values) <= allowed for values in axioms.values())
prints = re.findall(r"^#print axioms (\S+)$", source, re.M)
assert len(records) == len(prints) == 40, (len(records), len(prints))
main = "AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved"
assert main + " : GoalPos1" in log
assert re.search(r"^theorem goalPos1_proved : GoalPos1 := by$", source, re.M)
local_theorems = re.findall(r"^theorem (\S+)", source, re.M)
assert set(local_theorems) <= set(prints)
print(json.dumps({
    "source": str(attempt),
    "sha256": hashlib.sha256(attempt.read_bytes()).hexdigest(),
    "pin_sha256": hashlib.sha256(pin.read_bytes()).hexdigest(),
    "pin_declarations_verbatim": matching,
    "imports": imports,
    "forbidden_tokens": forbidden,
    "exit_code": exit_code,
    "main_declaration": main,
    "main_type": "AdalyFormal.AHP.Round2.S2Nonvacuity.GoalPos1",
    "axiom_record_count": len(records),
    "axioms": axioms,
    "all_local_theorems_printed": local_theorems,
}, indent=2))
