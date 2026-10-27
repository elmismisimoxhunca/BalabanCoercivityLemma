#!/usr/bin/env python3
"""Read-only source/log audit; writes its report only beside Attempt.lean.
Not a numerical operator model or a substitute for Lean checking.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / 'Attempt.lean'
PIN = HERE.parent / 'pin' / 'Statement.lean'
OLD = ROOT / 'AHP/round2/s3-normalisation/r1-prove/Attempt.lean'
s = SRC.read_text()
p = PIN.read_text()
old = OLD.read_text()
start = old.index('namespace AdalyFormal.Round2.S3Pin', old.index('end AdalyFormal.Round2.S3Pin'))
end = old.index('/-- The primary positive goal, with its original quantifiers unchanged. -/')
old_proof = old[start:end]
ns = ''
names = []
prints = []
for line in s.splitlines():
    m = re.match(r'namespace (\S+)', line)
    if m:
        ns = m[1]
    if line.startswith('end '):
        ns = ''
    m = re.match(r'(?:noncomputable )?(?:def|abbrev|lemma|theorem|inductive|structure) (\S+)', line)
    if m:
        names.append(ns + '.' + m[1])
    m = re.match(r'#print axioms (\S+)', line)
    if m:
        prints.append(m[1] if m[1].startswith('AdalyFormal.') else ns + '.' + m[1])
logpath = Path(str(SRC) + '.log')
exitpath = Path(str(SRC) + '.exit')
log = logpath.read_text() if logpath.exists() else ''
records = re.findall(r"^'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", log, re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad_axioms = [(name, ax) for name, ax in records if set(ax.replace('\n', '').replace(' ', '').split(',')) - allowed - {''}]
record_names = {name for name, _ in records}
main = 'AdalyFormal.Round3.S3Rest.goalPos2_proved'
report = {
    'source': str(SRC.relative_to(ROOT)),
    'sourceSha256': hashlib.sha256(SRC.read_bytes()).hexdigest(),
    'pinSha256': hashlib.sha256(PIN.read_bytes()).hexdigest(),
    'logSha256': hashlib.sha256(logpath.read_bytes()).hexdigest() if logpath.exists() else None,
    'pinByteIdenticalPrefix': s.startswith(p),
    'roundTwoProofBlockByteIdentical': old_proof in s,
    'imports': re.findall(r'^import (.*)$', s, re.M),
    'forbiddenRawHits': re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', s),
    'declarationCount': len(names),
    'explicitPrintCount': len(prints),
    'declarationsWithoutPrint': sorted(set(names) - set(prints)),
    'printsWithoutLogRecord': sorted(set(prints) - record_names),
    'dependencyRecordCount': len(records),
    'nonstandardDependencyRecords': bad_axioms,
    'errors': re.findall(r'^.*error:.*$', log, re.M),
    'warnings': len(re.findall(r'^.*warning:.*$', log, re.M)),
    'exitCode': int(exitpath.read_text().strip()) if exitpath.exists() else None,
    'mainDeclaration': main,
    'exactMainHeader': 'theorem goalPos2_proved : GoalPos2 := by' in s,
    'mainAxiomLine': next((line for line in log.splitlines() if line.startswith("'" + main + "'")), None),
}
report['passes'] = all([
    report['pinByteIdenticalPrefix'], report['roundTwoProofBlockByteIdentical'],
    report['imports'] == ['ZT5A'], not report['forbiddenRawHits'],
    not report['declarationsWithoutPrint'], not report['printsWithoutLogRecord'],
    not report['nonstandardDependencyRecords'], not report['errors'],
    report['exitCode'] == 0, report['exactMainHeader'], bool(report['mainAxiomLine']),
])
(HERE / 'AUDIT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(0 if report['passes'] else 1)
