#!/usr/bin/env python3
"""Read-only artifact audit, emits JSON; does not invoke Lean."""
from pathlib import Path
import hashlib
import json
import re

base = Path(__file__).resolve().parent
src = base / 'Attempt.lean'
log = base / 'Attempt.lean.log'
code = src.read_text()
output = log.read_text()
pin = base.parent / 'pin' / 'Statement.lean'
expected = []
namespace = ''
for line in code.splitlines():
    if m := re.match(r'^namespace (\S+)', line):
        namespace = m[1]
    if m := re.match(r'^#print axioms (\S+)', line):
        name = m[1]
        expected.append(name if name.startswith('AdalyFormal.') else namespace + '.' + name)
    if line.startswith('end '):
        namespace = ''
records = dict(re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", output, re.M))
for name in re.findall(r"^'([^\n]+)' does not depend on any axioms", output, re.M):
    records[name] = ''
allowed = {'propext','Classical.choice','Quot.sound'}
bad = {n: [a.strip() for a in ax.split(',') if a.strip() and a.strip() not in allowed]
       for n, ax in records.items()}
bad = {n: ax for n, ax in bad.items() if ax}
report = {
    'exitCode': int((base / 'Attempt.lean.exit').read_text().strip()),
    'pinByteIdenticalPrefix': src.read_bytes().startswith(pin.read_bytes()),
    'soleImport': re.findall(r'^import (.+)$', code, re.M),
    'requestedAxiomRecords': len(expected),
    'seenAxiomRecords': len(records),
    'missingAxiomRecords': [n for n in expected if n not in records],
    'disallowedAxioms': bad,
    'forbiddenTokensRaw': re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', code),
    'errorLines': [s for s in output.splitlines() if re.search(r': error(?:\(|:)', s)],
    'warningCount': len(re.findall(r': warning:', output)),
    'mainDeclaration': 'AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible',
    'mainAxioms': records.get('AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible'),
    'sourceSha256': hashlib.sha256(src.read_bytes()).hexdigest(),
    'logSha256': hashlib.sha256(log.read_bytes()).hexdigest(),
    'pinSha256': hashlib.sha256(pin.read_bytes()).hexdigest(),
}
report['passed'] = (report['exitCode'] == 0 and report['pinByteIdenticalPrefix']
    and report['soleImport'] == ['ZT5A'] and not report['missingAxiomRecords']
    and not report['disallowedAxioms'] and not report['forbiddenTokensRaw']
    and not report['errorLines'] and report['mainAxioms'] is not None)
print(json.dumps(report, indent=2))
raise SystemExit(0 if report['passed'] else 1)
