#!/usr/bin/env python3
"""Audit current Lean source and wrapper evidence; write only the local report.
This is a source/log consistency check, not a replacement for Lean compilation.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "Attempt.lean"
PIN = ROOT / "AHP/round3/s3-rest/pin/Statement.lean"
NORMALIZED = ROOT / "AHP/round3/s3-rest/r1-prove/Attempt.lean"
LOG = HERE / "Attempt.lean.log"
EXIT = HERE / "Attempt.lean.exit"
source_bytes = SRC.read_bytes()
source = source_bytes.decode()
log = LOG.read_text()
namespace = ""
declarations = []
prints = []
for line in source.splitlines():
    match = re.match(r"namespace (\S+)", line)
    if match:
        namespace = match[1]
    if line.startswith("end "):
        namespace = ""
    match = re.match(r"(?:noncomputable )?(?:def|abbrev|lemma|theorem|inductive|structure) (\S+)", line)
    if match:
        declarations.append(namespace + "." + match[1])
    match = re.match(r"#print axioms (\S+)", line)
    if match:
        name = match[1]
        prints.append(name if name.startswith("AdalyFormal.") else namespace + "." + name)
records = re.findall(
    r"^'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",
    log, re.M,
)
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad_records = [
    (name, deps) for name, deps in records
    if {dep.strip() for dep in deps.split(",") if dep.strip()} - allowed
]
record_names = {name for name, _ in records}
main = "AdalyFormal.Round3.S3Rest.goalPos1_proved"
report = {
    "source": str(SRC.relative_to(ROOT)),
    "hashesSha256": {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (SRC, PIN, NORMALIZED, LOG, EXIT)
    },
    "pinByteIdenticalPrefix": source_bytes.startswith(PIN.read_bytes()),
    "entireNormalizedAttemptByteIdenticalPrefix": source_bytes.startswith(NORMALIZED.read_bytes()),
    "imports": re.findall(r"^import (.*)$", source, re.M),
    "forbiddenRawHits": re.findall(
        r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b", source
    ),
    "declarationCount": len(declarations),
    "explicitPrintCount": len(prints),
    "declarationsWithoutPrint": sorted(set(declarations) - set(prints)),
    "printsWithoutLogRecord": sorted(set(prints) - record_names),
    "dependencyRecordCount": len(records),
    "nonstandardDependencyRecords": bad_records,
    "errors": re.findall(r"^.*error:.*$", log, re.M),
    "warningCount": len(re.findall(r"^.*warning:.*$", log, re.M)),
    "exitCode": int(EXIT.read_text().strip()),
    "exactMainHeader": "theorem goalPos1_proved : GoalPos1 :=\n" in source,
    "mainDeclaration": main,
    "mainAxiomLine": next((line for line in log.splitlines() if line.startswith("'" + main + "'")), None),
}
report["passes"] = all([
    report["pinByteIdenticalPrefix"], report["entireNormalizedAttemptByteIdenticalPrefix"],
    report["imports"] == ["ZT5A"], not report["forbiddenRawHits"],
    not report["declarationsWithoutPrint"], not report["printsWithoutLogRecord"],
    report["declarationCount"] == report["explicitPrintCount"] == report["dependencyRecordCount"],
    not report["nonstandardDependencyRecords"], not report["errors"],
    report["exitCode"] == 0, report["exactMainHeader"], bool(report["mainAxiomLine"]),
])
(HERE / "AUDIT.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
raise SystemExit(0 if report["passes"] else 1)
