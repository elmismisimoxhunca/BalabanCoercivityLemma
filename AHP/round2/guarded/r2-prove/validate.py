#!/usr/bin/env python3
"""Static/source/log audit only; does not run Lean or numerical operators."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
PIN = HERE.parent / "pin" / "Statement.lean"
SOURCE = HERE / "Attempt.lean"
raw = SOURCE.read_bytes()
text = raw.decode()
log = (HERE / "Attempt.lean.log").read_text()
exit_code = int((HERE / "Attempt.lean.exit").read_text().strip())
allowed = {"propext", "Classical.choice", "Quot.sound"}
pattern = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)
records = {
    name: sorted(x.strip() for x in (ax or "").replace("\n", " ").split(",") if x.strip())
    for name, ax in pattern.findall(log)
}
forbidden = re.findall(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b", text
)
imports = re.findall(r"^import\s+(.+)$", text, re.MULTILINE)
declarations = re.findall(
    r"^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+([^\s:(]+)",
    text,
    re.MULTILINE,
)
local_records = {
    name: ax for name, ax in records.items()
    if name.startswith("AdalyFormal.Round2.Guarded.")
}
missing = sorted({name for name in declarations if not any(
    full.endswith("." + name) for full in local_records
)})
prints = re.findall(r"^#print axioms\s+(\S+)", text, re.MULTILINE)
main = "AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response"
main_line = next(i for i, line in enumerate(text.splitlines(), 1)
                 if line.startswith("theorem goalPos2_iff_boundary_response"))
lines = {name: next(i for i, line in enumerate(text.splitlines(), 1)
                   if re.match(r"(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+"
                               + re.escape(name) + r"(?:\s|:|\(|$)", line))
         for name in declarations}
result = {
    "source": str(SOURCE.relative_to(HERE.parents[3])),
    "sha256": hashlib.sha256(raw).hexdigest(),
    "exact_pin_byte_prefix": raw.startswith(PIN.read_bytes()),
    "imports": imports,
    "exitCode": exit_code,
    "exit_newer_than_log": (HERE / "Attempt.lean.exit").stat().st_mtime_ns >=
        (HERE / "Attempt.lean.log").stat().st_mtime_ns,
    "log_newer_than_source": (HERE / "Attempt.lean.log").stat().st_mtime_ns >= SOURCE.stat().st_mtime_ns,
    "errors_or_warnings": re.findall(r"^.*(?:error|warning):.*$", log, re.MULTILINE),
    "forbidden_tokens": forbidden,
    "print_requests": len(prints),
    "dependency_records": len(records),
    "local_declarations": len(declarations),
    "local_dependency_records": len(local_records),
    "missing_local_prints": missing,
    "disallowed_dependencies": {n: a for n, a in records.items() if not set(a) <= allowed},
    "mainDeclaration": main,
    "mainLine": main_line,
    "mainAxioms": records.get(main),
    "declarationLines": lines,
    "closedGoal": "none",
}
assert result["exact_pin_byte_prefix"]
assert imports == ["DrEquiv"]
assert exit_code == 0
assert result["exit_newer_than_log"] and result["log_newer_than_source"]
assert not result["errors_or_warnings"]
assert not forbidden and not missing and not result["disallowed_dependencies"]
assert len(prints) == len(records)
assert len(declarations) == len(local_records)
assert main in records
(HERE / "VALIDATION.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
