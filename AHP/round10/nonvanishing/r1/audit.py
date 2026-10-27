#!/usr/bin/env python3
"""Audit final R10 nonvanishing sources and the independently compiled hand-off copies."""
from pathlib import Path
import hashlib
import json
import re

base = Path(__file__).resolve().parent
root = base.parents[3]
shared = root / 'AHP/round10/shared/nonvanishing'
names = ['SourceDominance', 'RecurrenceNonvanishing', 'TransferNonvanishing']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
namespace = 'AdalyFormal.Round10.Nonvanishing.'
reports = []
for name in names:
    original = base / (name + '.lean')
    handoff = shared / ('R1_' + name + '.lean')
    assert original.read_bytes() == handoff.read_bytes()
    for path in [original, handoff]:
        source = path.read_text()
        logpath = Path(str(path) + '.log')
        exitpath = Path(str(path) + '.exit')
        log = logpath.read_text()
        declarations = re.findall(r'^(?:def|lemma|theorem)\s+(\w+)', source, re.M)
        records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
        dependencies = {n: [x.strip() for x in deps.split(',') if x.strip()] for n, deps in records}
        checks = {
            'exit_zero': exitpath.read_text().strip() == '0',
            'only_frozen_import': re.findall(r'^import (.+)$', source, re.M) == ['D1IVT'],
            'no_forbidden_tokens': not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source),
            'no_errors_or_warnings': not re.search(r'\b(error|warning):|sorryAx', log),
            'standard_axioms_only': all(set(ds) <= allowed for ds in dependencies.values()),
            'every_declaration_printed': all(namespace + d in dependencies for d in declarations),
            'record_count_matches': len(declarations) == len(records),
            'timestamps_current': path.stat().st_mtime_ns <= logpath.stat().st_mtime_ns <= exitpath.stat().st_mtime_ns,
        }
        reports.append({
            'file': str(path.relative_to(root)),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'declarations': len(declarations),
            'checks': checks,
            'pass': all(checks.values()),
            'axioms': dependencies,
        })
report = {
    'status': 'conditional-infrastructure-only',
    'goalNeg2_proved': False,
    'distinct_source_files': len(names),
    'distinct_declarations': sum(r['declarations'] for r in reports[::2]),
    'independently_compiled_files': len(reports),
    'byte_identical_handoffs': True,
    'pass': all(r['pass'] for r in reports),
    'files': reports,
}
(base / 'CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))
if not report['pass']:
    raise SystemExit(1)
