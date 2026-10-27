#!/usr/bin/env python3
"""Static evidence audit; this does not invoke Lean or certify new declarations."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
TRACK = ROOT.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def deps(text):
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    return [{'name': name, 'axioms': [v.strip() for v in values.split(',') if v.strip()]}
            for name, values in matches]


pin = (TRACK / 'pin/Statement.lean').read_bytes()
partial = (TRACK / 'attempt/Partial.lean').read_bytes()
body = partial.removeprefix(b'import SoA3\nimport SoPar\n')
source = (ROOT / 'Attempt.lean').read_bytes()
assert source.startswith(pin + b'\n' + body)
assert sha(TRACK / 'pin/Statement.lean') == '27a16f875b66d6fce71129ca3b0c08f1e4579fcac86fc742b1c186ffc00385ab'
assert partial == (TRACK / 'verify/Partial.lean').read_bytes()
prior = []
for rel in ('attempt/Partial.lean', 'verify/Partial.lean'):
    p = TRACK / rel
    log = Path(str(p) + '.log')
    exitfile = Path(str(p) + '.exit')
    assert exitfile.read_text().strip() == '0'
    assert p.stat().st_mtime <= log.stat().st_mtime <= exitfile.stat().st_mtime
    records = deps(log.read_text())
    assert len(records) == 21
    assert all(set(r['axioms']) <= ALLOWED for r in records)
    assert 'error:' not in log.read_text()
    prior.append({'source': str(p), 'sha256': sha(p), 'exitCode': 0,
                  'logSha256': sha(log), 'dependencyRecords': records,
                  'provenance': 'pre-existing builder/replay, not this attack'})

files = []
for name in ('Attempt.lean', 'BlockingCertificate.lean', 'GuardedGeometry.lean'):
    p = ROOT / name
    text = p.read_text()
    imports = re.findall(r'^import\s+(\S+)', text, re.M)
    assert imports == ['SoA3', 'SoPar']
    assert p.read_bytes().startswith(pin)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
    assert not forbidden
    declarations = re.findall(r'^(?:(?:noncomputable|private)\s+)*(?:def|abbrev|theorem)\s+(\w+)', text, re.M)
    prints = re.findall(r'^#print axioms\s+(\w+)', text, re.M)
    assert set(declarations) <= set(prints), set(declarations) - set(prints)
    exitfile = Path(str(p) + '.exit')
    assert not exitfile.exists(), 'A fresh exit appeared; inspect before publishing this audit.'
    files.append({'file': str(p), 'sha256': sha(p), 'pinVerbatimPrefix': True,
                  'imports': imports, 'forbiddenTokenHits': forbidden,
                  'localDeclarationCount': len(declarations),
                  'printCommandCount': len(prints),
                  'missingLocalPrints': sorted(set(declarations) - set(prints)),
                  'exitCode': None, 'verifiedCompilation': False})

result = {'status': 'OPEN; no new compiled result', 'closedGoal': 'none',
          'pinSha256': sha(TRACK / 'pin/Statement.lean'),
          'attemptIncludesVerbatimInheritedPartial': True,
          'priorSuccessfulPartialChecks': prior, 'currentFiles': files,
          'mainPreviouslyCompiledDeclaration': 'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class',
          'limitations': ['Static audit is not compilation.',
                         'New blocking/H0 and full-guard coverage drafts are unverified.',
                         'No odd-scale analytic goal is proved or refuted.']}
(ROOT / 'AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'staticAudit': 'pass', 'newCompilation': 'unverified',
                  'priorPartialRecords': [len(p['dependencyRecords']) for p in prior],
                  'currentLocalDeclarations': [p['localDeclarationCount'] for p in files],
                  'closedGoal': 'none'}, indent=2))
