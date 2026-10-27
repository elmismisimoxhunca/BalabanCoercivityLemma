#!/usr/bin/env python3
"""Source/provenance audit only. Does NOT invent a completed Lean log."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
src = HERE / 'Attempt.lean'
pin = ROOT / 'AHP/round3/guarded/pin/Statement.lean'
old = ROOT / 'AHP/round5/guarded/ivt-r2/Attempt.lean'
s = src.read_text()
assert src.read_bytes().startswith(pin.read_bytes())
assert src.read_bytes() == old.read_bytes() + (HERE / 'Appendix.lean').read_bytes()
assert re.findall(r'^import (.+)$', s, re.M) == ['DrEquiv']
assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', s)
decls = re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)", s, re.M)
prints = re.findall(r"^#print axioms ([\w.']+)", s, re.M)
assert all(any(p == d or p.endswith('.' + d) for p in prints) for d in decls)
lines = {d: i for i, line in enumerate(s.splitlines(), 1)
         for d in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)", line)}
log = (HERE / 'BoundaryDraft.interrupted.log').read_text()
rec = re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all({a.strip() for a in ax.split(',') if a.strip()} <= allowed for _, ax in rec)
meta = json.loads((HERE / 'VERIFICATION.json').read_text())
assert hashlib.sha256(src.read_bytes()).hexdigest() == meta['finalSourceSha256']
assert (HERE / 'PriorSuccessfulRun.exit').read_text().strip() == '0'
assert not (HERE / 'Attempt.lean.exit').exists()
assert not (HERE / 'Attempt.lean.log').exists()
assert not meta['timedOutRunRelaunched']
result = dict(
    closedGoal='none',
    sourceSha256=meta['finalSourceSha256'],
    pinVerbatimBytePrefix=True,
    round5BridgeVerbatimBytePrefix=True,
    onlyFrozenImports=True,
    forbiddenTokens=[],
    localDeclarationCount=len(decls),
    everyLocalDeclarationHasPrintCommand=True,
    newDeclarations={n: l for n, l in lines.items() if l > len(old.read_text().splitlines())},
    priorExactSourceCompileExit=0,
    priorCompleteLogPreserved=False,
    freshFinalCompileExit=None,
    interruptedDraftDependencyRecords=len(rec),
    interruptedDraftRecordsAllPermitted=True,
    completeFinalDependencyAudit=False,
    numericalJobsRun=0,
    scope='Source/provenance checks passed. Not a fresh final compile or complete retained axiom audit. No positive-amplitude obstruction established.'
)
(HERE / 'CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
