#!/usr/bin/env python3
"""Repair only the omitted helper copies in the historical round-10 join."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
old = ROOT / 'AHP/round10/assembly/r4/Attempt.lean'
dictionary = ROOT / 'AHP/round10/shared/dictionary/R4_ColorResponse.lean'
s = old.read_text()
d = dictionary.read_text()
header = d[d.index('namespace AdalyFormal.Round10.Dictionary.FreeSource\n'):d.index('theorem circulation_congr_boundary')]
spans = [('theorem phase_axis_fixed', 'theorem sourceLinear_U1'), ('theorem half_twice', '/-- Actual carrier Q intertwines')]
helpers = []
records = []
for start, stop in spans:
    a = d.index(start); b = d.index(stop, a)
    text = d[a:b]
    helpers.append(text)
    records.append({'source': str(dictionary.relative_to(ROOT)), 'start_line': d[:a].count('\n')+1, 'end_line_exclusive': d[:b].count('\n')+1, 'sha256': hashlib.sha256(text.encode()).hexdigest()})
insert = header + '\n'.join(helpers) + '\n#print axioms phase_axis_fixed\n#print axioms half_twice\n#print axioms half_average\nend AdalyFormal.Round10.Dictionary.FreeSource\n\n'
marker = 'noncomputable section\nnamespace AdalyFormal.Round10.Dictionary.Color\n'
assert s.count(marker) == 1
result = s.replace(marker, insert + marker)
assert result.replace(insert, '', 1) == s
out = HERE / 'RepairedJoin.lean'
out.write_text(result)
(HERE / 'REPAIR_COPIES.json').write_text(json.dumps({'original': str(old.relative_to(ROOT)), 'original_sha256': hashlib.sha256(s.encode()).hexdigest(), 'output_sha256': hashlib.sha256(result.encode()).hexdigest(), 'only_change': 'insert namespace/header and three verbatim helpers immediately before Color section, with axiom prints', 'helpers': records}, indent=2)+'\n')
print(out, len(result.splitlines()), 'lines')
