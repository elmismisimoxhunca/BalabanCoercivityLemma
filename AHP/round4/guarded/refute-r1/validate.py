#!/usr/bin/env python3
"""Audit the final Lean artifact; no numerical or spectral certification."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
source_path = HERE / 'Attempt.lean'
source = source_path.read_text()
pin = ROOT / 'AHP/round3/guarded/pin/Statement.lean'
previous = ROOT / 'AHP/round3/guarded/r3-refute/Attempt.lean'
assert source_path.read_bytes().startswith(pin.read_bytes()), 'changed pin'
assert source_path.read_bytes().startswith(previous.read_bytes()), 'changed inherited attempt'
imports = re.findall(r'^import (.+)$', source, re.M)
assert imports == ['DrEquiv'], imports
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source)
assert not forbidden, forbidden
exit_path = HERE / 'Attempt.lean.exit'
log_path = HERE / 'Attempt.lean.log'
assert exit_path.read_text().strip() == '0'
log = log_path.read_text()
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:', log), 'diagnostic in final log'
records = re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.M)
assert records
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in records:
    assert {a.strip() for a in axioms.split(',') if a.strip()} <= allowed, (name, axioms)
local_decls = re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)", source, re.M)
seen = {n for n, _ in records}
assert all(any(n.endswith('.' + d) for n in seen) for d in local_decls), 'missing local dependency print'
main = 'AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor'
assert main in seen
assert source_path.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
lines = {d: i for i, line in enumerate(source.splitlines(), 1)
         for d in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)", line)}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
result = {
    'closedGoal': 'none',
    'file': str(source_path.relative_to(ROOT)),
    'mainDeclaration': main,
    'mainLine': lines[main.split('.')[-1]],
    'axiomLine': next(f"'{n}' depends on axioms: [{', '.join(a.strip() for a in ax.split(','))}]"
                      for n, ax in records if n == main),
    'compileExit': 0,
    'warningCount': 0,
    'imports': imports,
    'pinVerbatimBytePrefix': True,
    'inheritedRound3AttemptVerbatimBytePrefix': True,
    'sourceSha256': sha(source_path),
    'pinSha256': sha(pin),
    'inheritedAttemptSha256': sha(previous),
    'logSha256': sha(log_path),
    'localDeclarationCount': len(local_decls),
    'printedDependencyRecords': len(records),
    'allLocalDeclarationsPrinted': True,
    'allAxiomsAllowed': True,
    'forbiddenTokens': forbidden,
    'newDeclarations': {name: line for name, line in lines.items()
                        if line > len(previous.read_text().splitlines())},
    'numericsRun': False,
    'scope': 'Cofinal nonspectral class/geometry/competitor certificate with an exact nontrivial interior holonomy and no global flattening gauge. No carrier guard or corrected singularity is proved. No pinned goal is closed.',
    'independentReplay': False,
}
(HERE / 'CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
