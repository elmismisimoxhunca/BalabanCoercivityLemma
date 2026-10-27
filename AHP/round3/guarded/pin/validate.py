#!/usr/bin/env python3
"""Static artifact audit only; no numerical operator model and no Lean invocation."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "Statement.lean"
raw = SOURCE.read_bytes()
text = raw.decode()
old_path = ROOT / "AHP/round2/guarded/pin/Statement.lean"
old = old_path.read_bytes()
assert raw.startswith(old), "Round-2 pin is not an exact byte prefix"


def declaration(source, name):
    lines = source.splitlines()
    pattern = re.compile(r"^(?:noncomputable )?(?:abbrev|def|theorem) " + re.escape(name) + r"\b")
    starts = [i for i, line in enumerate(lines) if pattern.match(line)]
    assert len(starts) == 1, (name, starts)
    start = starts[0]
    stop = start + 1
    while stop < len(lines) and lines[stop] and lines[stop][0].isspace():
        stop += 1
    return "\n".join(lines[start:stop]), start + 1


copies = {
    "lean/src/D1Lit.lean": [
        "PlaqSel", "selIn", "selAll", "DeltaS", "DpiFullS", "DpiFullS_symm",
        "JfS", "dataS", "dataS_laws", "G1invS", "H1inS", "NmatS", "firstTermS", "genFormS", "InstIneqS",
    ],
    "lean/src/D2Cons.lean": ["InstIneqSG", "CoercG8AtSG", "P428Target8SG"],
    "lean/src/GdR5a.lean": ["GuardResidualT"],
    "lean/src/DrEquiv.lean": ["GShape", "CPen", "GuardPencilT"],
    "AHP/round2/guarded/r2-prove/Attempt.lean": [
        "response", "boundaryShift", "localCorrected", "CBoundaryResponse", "CNoBoundaryReturn",
    ],
}
copy_checks = []
for path, names in copies.items():
    original = (ROOT / path).read_text()
    for name in names:
        copied, line = declaration(text, name)
        reference, original_line = declaration(original, name)
        assert copied == reference, (path, name, "not verbatim")
        copy_checks.append({"name": name, "line": line, "source": path,
                            "sourceLine": original_line, "verbatim": True})

for n in (1, 2):
    assert declaration(text, f"GoalNeg{n}")[0] == f"def GoalNeg{n} : Prop := ¬ GoalPos{n}"
imports = re.findall(r"^import (\S+)\s*$", text, re.M)
assert imports == ["DrEquiv"]
assert (ROOT / "lean/src/DrEquiv.lean").is_file()
forbidden = re.findall(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b", text)
assert not forbidden, forbidden

log_path = HERE / "Statement.lean.log"
exit_path = HERE / "Statement.lean.exit"
exit_code = int(exit_path.read_text().strip())
assert exit_code == 0
assert SOURCE.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
log = log_path.read_text()
diagnostics = re.findall(r"^.*\b(?:warning|error):.*$", log, re.M)
assert not diagnostics, diagnostics
pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
records = [{"declaration": m.group(1), "axioms": [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]}
           for m in pattern.finditer(log)]
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert all(set(row["axioms"]) <= allowed for row in records)
requests = re.findall(r"^#print axioms (\S+)\s*$", text, re.M)
locals_ = re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem) (\S+)\s", text, re.M)
assert len(requests) == len(records) == len(locals_) == 42
for name in requests + locals_:
    assert sum(row["declaration"] == name or row["declaration"].endswith("." + name)
               for row in records) == 1, name

result = {
    "checksPass": True,
    "statementFile": str(SOURCE.relative_to(ROOT)),
    "sha256": hashlib.sha256(raw).hexdigest(),
    "round2Pin": str(old_path.relative_to(ROOT)),
    "round2PinSHA256": hashlib.sha256(old).hexdigest(),
    "round2PinExactBytePrefix": True,
    "round2PinLines": len(old.decode().splitlines()),
    "verbatimCopiedDeclarations": copy_checks,
    "negativeGoalsAreExactNegations": True,
    "imports": imports,
    "forbiddenTokensRawWholeSource": forbidden,
    "command": "AHP/round3/lean1.sh AHP/round3/guarded/pin/Statement.lean",
    "exitCode": exit_code,
    "diagnostics": diagnostics,
    "axiomRecordCount": len(records),
    "allLocalDeclarationsPrinted": True,
    "allAxiomsStandard": True,
    "records": records,
    "limitation": "A compiled statement contract, not a proof of either positive or negative goal. No numerical replay or full build; no independent second-agent audit claimed.",
}
(HERE / "CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: result[key] for key in ["checksPass", "sha256", "round2PinExactBytePrefix", "exitCode", "axiomRecordCount", "allAxiomsStandard"]}, indent=2))
print(f"{len(copy_checks)} verbatim declarations checked; evidence: {HERE / 'CHECKS.json'}")
