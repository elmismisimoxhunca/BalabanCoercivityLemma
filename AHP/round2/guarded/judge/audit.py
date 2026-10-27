#!/usr/bin/env python3
"""Read-only checks of sources/logs; writes evidence only beside this script.
This is an artifact audit, not a numerical model or a proof of any pinned goal.
"""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ITEM = HERE.parent
ROOT = ITEM.parents[2]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b")
AXIOMS = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
PIN = (ITEM / "pin/Statement.lean").read_bytes()
ENTRIES = [
    ("pin", "Statement.lean", 17, "AdalyFormal.Round2.Guarded.Pin.goalPos2_iff_goalPos1"),
    ("r1-prove", "Attempt.lean", 56, "AdalyFormal.Round2.Guarded.R1Prove.goalPos2_iff_boundary_kernel"),
    ("r1-refute", "Attempt.lean", 28, "AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet"),
    ("r2-prove", "Attempt.lean", 71, "AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response"),
    ("r2-refute", "Attempt.lean", 54, "AdalyFormal.Round2.Guarded.RefuteR2.goalNeg2_iff_cofinalPencilFailure"),
]
rows = []
for name, filename, expected, main in ENTRIES:
    original = ITEM / name / filename
    snapshot = HERE / name / filename
    raw = original.read_bytes()
    assert raw == snapshot.read_bytes(), f"Snapshot differs: {name}"
    source = raw.decode()
    copied_pin = source.replace("import GdR6b\n", "", 1) if name == "r1-refute" else source
    assert copied_pin.startswith(PIN.decode()), f"Pin differs: {name}"
    imports = re.findall(r"^import (\S+)\s*$", source, re.M)
    assert imports == (["DrEquiv", "GdR6b"] if name == "r1-refute" else ["DrEquiv"]), imports
    assert all((ROOT / "lean/src" / (imp.replace(".", "/") + ".lean")).is_file() for imp in imports)
    forbidden = sorted(set(FORBIDDEN.findall(source)))
    assert not forbidden, (name, forbidden)
    log_path = Path(str(snapshot) + ".log")
    exit_path = Path(str(snapshot) + ".exit")
    log = log_path.read_text()
    code = int(exit_path.read_text().strip())
    assert code == 0, (name, code)
    assert snapshot.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
    diagnostics = re.findall(r"^.*\b(?:warning|error):.*$", log, re.M)
    assert not diagnostics, (name, diagnostics)
    records = [(m.group(1), sorted(x.strip() for x in (m.group(2) or "").split(",") if x.strip()), m.group(0))
               for m in AXIOMS.finditer(log)]
    assert len(records) == expected, (name, len(records))
    assert all(set(deps) <= ALLOWED for _, deps, _ in records)
    requests = re.findall(r"^#print axioms (\S+)\s*$", source, re.M)
    assert len(requests) == len(records)
    assert all(any(full == req or full.endswith("." + req) for full, _, _ in records) for req in requests)
    main_record = next(record for full, _, record in records if full == main)
    rows.append({
        "source": str(original.relative_to(ROOT)),
        "compiledCopy": str(snapshot.relative_to(ROOT)),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "sourceEqualsCompiledCopy": True,
        "pinPrefixMatchesAfterRemovingOnlyExtraImport": True,
        "extraFrozenImportAtLine2": name == "r1-refute",
        "imports": imports,
        "forbiddenTokens": forbidden,
        "recompiledExit": code,
        "diagnostics": diagnostics,
        "axiomRecords": len(records),
        "allAxiomsStandard": True,
        "allRequestedPrintsPresent": True,
        "mainDeclaration": main,
        "mainAxiomLineNormalized": " ".join(main_record.split()),
    })
result = {
    "date": "2026-10-21",
    "checksPass": True,
    "axiomRecordsIncludingRepeatedPinRecords": sum(row["axiomRecords"] for row in rows),
    "files": rows,
    "limitation": "Compilation verifies the recorded reductions and exclusions, not either side of an open equivalence. No numerical replay or whole-project rebuild.",
}
(HERE / "CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
