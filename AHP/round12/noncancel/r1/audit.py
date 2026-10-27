#!/usr/bin/env python3
"""Audit actual exit files, complete axiom logs, source imports, and publication."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[4]
local = root / 'AHP/round12/noncancel/r1'
shared = root / 'AHP/round12/shared/noncancel/R1_Star.lean'
files = [local / (s + '.lean') for s in ['StarKernel', 'Plaquette', 'Trace', 'Attempt']] + [shared]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
report = []
for path in files:
    source = path.read_text()
    log = Path(str(path)+'.log').read_text()
    assert Path(str(path)+'.exit').read_text().strip() == '0', path
    assert 'error:' not in log and 'error(' not in log and 'sorryAx' not in log, path
    code = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', code), path
    assert re.findall(r'^import (.+)$', source, re.M) == ['DrEquiv'], path
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    expected = len(re.findall(r'^#print axioms ', source, re.M))
    assert len(matches) == expected and expected > 0, (path, len(matches), expected)
    names = []
    for name, axioms in matches:
        actual = set(filter(None, [x.strip() for x in axioms.split(',')]))
        assert actual <= allowed, (name, actual)
        names.append(name)
    resources = json.loads(Path(str(path)+'.resources.json').read_text())
    assert resources['exit'] == 0 and resources['rss_below_8_GiB'], path
    report.append({'file': str(path.relative_to(root)), 'exit': 0,
      'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
      'axiom_records': len(matches), 'all_axioms_standard': True,
      'declarations': names, 'resources': resources})
assert shared.read_bytes() == (local/'Attempt.lean').read_bytes()
upstream = (root/'AHP/round10/shared/assembly/R4_ResponseHull.lean').read_text()
for name in ['AnM', 'AnFam']:
    block = re.search(r'^def '+name+r'\b.*?(?=\n\n)', upstream, re.M | re.S).group(0)
    assert block in shared.read_text(), name
result = {'premise_closed': False, 'premise_disproved': False,
          'byte_identical_publication': True, 'copied_analytic_definitions_verbatim': True,
          'allowed_axioms': sorted(allowed), 'lean': report}
(local/'AUDIT.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'files': len(report), 'shared_axiom_records': report[-1]['axiom_records'],
  'all_exits_zero': True, 'all_axioms_standard': True, 'premise_closed': False}, indent=2))
