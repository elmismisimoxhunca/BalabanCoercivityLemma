#!/usr/bin/env python3
"""Audit the delivered exact copy against its actual completed wrapper run."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PIN = ROOT / 'AHP/round3/guarded/pin/Statement.lean'
PERMITTED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b'

def digest(b):
    return hashlib.sha256(b).hexdigest()

final = (HERE / 'Attempt.lean').read_bytes()
compiled = (HERE / 'DecayModel.lean').read_bytes()
pin = PIN.read_bytes()
assert final == compiled, 'Final file must be an exact copy, not an uncompiled extension'
assert final.startswith(pin), 'Pin changed'
assert not re.search(FORBIDDEN, final.decode())
assert re.findall(r'^import (.+)$', final.decode(), re.M) == ['DrEquiv']
logpath = HERE / 'DecayModel.lean.log'
exitpath = HERE / 'DecayModel.lean.exit'
log = logpath.read_text()
assert exitpath.read_text().strip() == '0'
assert (HERE / 'DecayModel.lean').stat().st_mtime_ns <= logpath.stat().st_mtime_ns <= exitpath.stat().st_mtime_ns
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*\))?:', log)
records = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log, re.S)
assert len(records) == 56
for name, deps in records:
    actual = {a.strip() for a in deps.split(',') if a.strip()}
    assert actual <= PERMITTED, (name, actual)
names = {n for n, _ in records}
source_names = re.findall(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma)\s+([^\s(:]+)', final.decode(), re.M)
for n in source_names:
    assert any(k.endswith('.' + n) for k in names), n
assert len(source_names) == 56
main = 'AdalyFormal.Round4.Guarded.DecayR2.Diagnostic.arbitrarily_small_separated_model'
assert main in names

draft = (HERE / 'KernelDraft.lean').read_bytes()
assert draft.startswith(pin)
assert not re.search(FORBIDDEN, draft.decode())
report = {
    'closedGoal': 'none',
    'finalFile': str(HERE / 'Attempt.lean'),
    'compiledCopy': str(HERE / 'DecayModel.lean'),
    'compilerCommand': 'AHP/round3/lean1.sh AHP/round5/guarded/kernel-r1/DecayModel.lean',
    'compiledCopyExit': 0,
    'finalExactCopy': final == compiled,
    'finalSHA256': digest(final),
    'pinSHA256': digest(pin),
    'pinIsExactPrefix': True,
    'imports': ['DrEquiv'],
    'allLocalDeclarationsPrinted': True,
    'localDeclarations': len(source_names),
    'dependencyRecords': len(records),
    'allDependenciesPermitted': True,
    'mainDeclaration': main,
    'mainAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'diagnostics': [],
    'forbiddenTokens': [],
    'finalPathRecompiled': False,
    'note': 'Attempt.lean is copied from the successful DecayModel.lean, not compiled after the timeout. No final-path log or exit was fabricated.',
    'kernelDraftSHA256': digest(draft),
    'kernelDraftAccepted': False,
    'kernelDraftStatus': 'Last direct wrapper call timed out while waiting for lock; log empty; old exit 1 predates edited source. No live kernel-route wrapper remained. Not relaunched.',
    'gapModelExit': int((HERE / 'GapModel.lean.exit').read_text()),
    'gapModelNote': 'Successful repaired version restored byte-for-byte after a warning-only edit; not recompiled after the timeout. Secondary evidence only.',
}
(HERE / 'CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
