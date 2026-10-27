#!/usr/bin/env python3
"""Check compilation artifacts and source fidelity; not a mathematical closure proof.
No numerical operator model or numerical job is run by this script.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = HERE / "Attempt.lean"
LOG = HERE / "Attempt.lean.log"
EXIT = HERE / "Attempt.lean.exit"
PIN = ROOT / "AHP/round3/guarded/pin/Statement.lean"
BRIDGE = ROOT / "AHP/round5/guarded/ivt-r2/Attempt.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MAIN = "AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry"
CONDITIONAL = "AdalyFormal.Round6.Guarded.ClosedFormR1.no_arbitrarily_small_control_of_negative_jet"


def without_comments(s):
    out = []
    depth = 0
    i = 0
    while i < len(s):
        if s[i:i+2] == "/-":
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and s[i:i+2] == "-/":
            depth -= 1
            out.extend("  ")
            i += 2
        elif not depth and s[i:i+2] == "--":
            while i < len(s) and s[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(s[i] if not depth or s[i] == "\n" else " ")
            i += 1
    assert depth == 0
    return "".join(out)


source = SRC.read_text()
assert SRC.read_bytes().startswith(PIN.read_bytes())
assert SRC.read_bytes().startswith(BRIDGE.read_bytes())
assert re.findall(r"^import (.+)$", source, re.M) == ["DrEquiv"]
assert not re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b", source)
assert EXIT.read_text().strip() == "0"
log = LOG.read_text()
assert not re.search(r"\b(?:error|warning)(?:\([^\n]*?\))?:", log)
assert SRC.stat().st_mtime_ns <= LOG.stat().st_mtime_ns <= EXIT.stat().st_mtime_ns
records = re.findall(
    r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    log, re.M,
)
assert records
seen = {}
for name, raw in records:
    deps = {x.strip() for x in raw.split(",") if x.strip()}
    assert deps <= ALLOWED, (name, deps)
    seen[name] = sorted(deps)

stack = []
declarations = {}
prints = []
for lineno, line in enumerate(without_comments(source).splitlines(), 1):
    s = line.strip()
    m = re.fullmatch(r"namespace ([\w.']+)", s)
    if m:
        stack.append(m[1])
        continue
    if re.fullmatch(r"(?:noncomputable )?section(?: [\w.']+)?", s):
        stack.append(None)
        continue
    if re.fullmatch(r"end(?: [\w.']+)?", s):
        assert stack, (lineno, s)
        stack.pop()
        continue
    ns = ".".join(x for x in stack if x)
    m = re.match(r"(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)", s)
    if m:
        name = f"{ns}.{m[1]}" if ns else m[1]
        assert name not in declarations, name
        declarations[name] = lineno
    m = re.fullmatch(r"#print axioms ([\w.']+)", s)
    if m:
        name = m[1]
        # Qualified external names and namespace-relative names both occur.
        candidates = [name] + [f"{ns}.{name}"]
        resolved = [x for x in candidates if x in seen]
        assert resolved, (lineno, name, ns)
        prints.append(resolved[0])
assert not stack
assert set(declarations) <= set(prints), sorted(set(declarations) - set(prints))
assert set(declarations) <= set(seen)
assert len(prints) == len(records)
assert MAIN in declarations and CONDITIONAL in declarations

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
bridge_lines = len(BRIDGE.read_text().splitlines())
result = {
    "closedGoal": "none",
    "file": str(SRC.relative_to(ROOT)),
    "compileExit": 0,
    "errorCount": 0,
    "warningCount": 0,
    "mainDeclaration": MAIN,
    "mainLine": declarations[MAIN],
    "mainAxioms": seen[MAIN],
    "mainScope": "Actual orthogonal carrier translation, link invariance and plaquette-word invariance; not operator commutation or block diagonalisation.",
    "conditionalDeclaration": CONDITIONAL,
    "conditionalLine": declarations[CONDITIONAL],
    "conditionalAxioms": seen[CONDITIONAL],
    "conditionalScope": "Negative leading coefficient plus whole-kernel remainder imply failure of arbitrarily small InitialKernelControl. Neither premise is evaluated for the family.",
    "imports": ["DrEquiv"],
    "pinVerbatimBytePrefix": True,
    "round5BridgeVerbatimBytePrefix": True,
    "sourceSha256": sha(SRC),
    "pinSha256": sha(PIN),
    "round5BridgeSha256": sha(BRIDGE),
    "logSha256": sha(LOG),
    "localDeclarationCount": len(declarations),
    "printedDependencyRecords": len(records),
    "allLocalDeclarationsPrinted": True,
    "allAxiomsAllowed": True,
    "newDeclarations": {n: l for n, l in declarations.items() if l > bridge_lines},
    "newDeclarationCount": sum(l > bridge_lines for l in declarations.values()),
    "numericalJobsRun": 0,
    "independentReplay": False,
}
(HERE / "CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
