"""Read-only audit of source/log evidence; writes only VERIFY.json in this track."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
repo = root.parents[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}
forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b")
rows = []
for rel in ("pin/Statement.lean", "attempt/Partial.lean", "verify/Statement.lean", "verify/Partial.lean"):
    path = root / rel
    src = path.read_text()
    log = Path(str(path) + ".log")
    exitfile = Path(str(path) + ".exit")
    out = log.read_text()
    records = {}
    for name, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", out, re.S):
        records[name] = [d.strip() for d in deps.split(",") if d.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", out):
        records[name] = []
    commands = re.findall(r"^#print axioms (\S+)", src, re.M)
    decls = re.findall(r"^(?:noncomputable )?(?:def|abbrev|theorem) (\S+)", src, re.M)
    assert set(commands) == set(decls), (rel, set(decls) - set(commands))
    assert len(commands) == len(records), (rel, len(commands), len(records))
    assert {name.rsplit(".", 1)[1] for name in records} == set(commands)
    assert all(set(deps) <= allowed for deps in records.values()), records
    assert exitfile.read_text().strip() == "0", rel
    assert not re.search(r"\berror:|\bwarning:|sorryAx", out), rel
    assert not forbidden.search(src), rel
    assert path.stat().st_mtime_ns <= log.stat().st_mtime_ns <= exitfile.stat().st_mtime_ns, rel
    imports = re.findall(r"^import (\S+)", src, re.M)
    assert imports == ["SoA3", "SoPar"], (rel, imports)
    assert all((repo / "lean/src" / (name.replace(".", "/") + ".lean")).exists() for name in imports)
    rows.append({
        "file": str(path.relative_to(repo)),
        "sourceSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        "exitCode": 0,
        "printedDeclarations": len(records),
        "diagnostics": 0,
        "rawForbiddenMatches": 0,
        "sourceBeforeLogBeforeExit": True,
        "imports": imports,
        "axioms": records,
    })
for original, replay in (("pin/Statement.lean", "verify/Statement.lean"), ("attempt/Partial.lean", "verify/Partial.lean")):
    assert (root / original).read_bytes() == (root / replay).read_bytes()

def body(text):
    return "def FamilyTorusSitesConstAt" + text.split("def FamilyTorusSitesConstAt", 1)[1].split("\n\n", 1)[0]
assert body((root / "pin/Statement.lean").read_text()) == body((repo / "lean/src/CaT2d.lean").read_text())
report = {
    "status": "pass",
    "analyticStatus": "open",
    "goalsClosed": [],
    "bodyVerbatimFromFrozen": True,
    "byteIdenticalBuilderReplays": True,
    "verificationScope": "serial wrapper compilations and read-only audit; no independent reviewer or full rebuild",
    "files": rows,
}
(root / "VERIFY.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"status": "pass", "files": len(rows), "printedRecordsIncludingReplays": sum(r["printedDeclarations"] for r in rows), "goalsClosed": []}, indent=2))
