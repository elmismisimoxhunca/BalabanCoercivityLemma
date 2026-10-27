#!/usr/bin/env python3
"""Read-only check of the new jet-domination hypothesis against retained R9 data.
This is floating-point evidence, not a proof or an interval certificate.
"""
import json
from pathlib import Path
from decimal import Decimal, getcontext

getcontext().prec = 65
root = Path(__file__).resolve().parents[4]
source = root / 'AHP/round9/analytic-r1/numerics/out/terms_left_R8_p50.json'
rows = json.loads(source.read_text())
report = []
for row in rows:
    terms = row['terms']
    jets = [Decimal(str(t['term'])) / Decimal(str(t['h'])) for t in terms]
    ratios = [abs(x / jets[0]) for x in jets]
    tail = ratios[1:]
    report.append({
        'k': row['k'],
        'root': row['root'],
        'number_of_terms': len(terms),
        'max_abs_jet_ratio_including_root': str(max(ratios)),
        'max_abs_jet_ratio_excluding_root': str(max(tail)),
        'all_jets_bounded_by_first': all(x <= 1 for x in ratios),
        'first_jet_nonzero_floating_point': jets[0] != 0,
        'pairing_to_first_term': str(Decimal(str(row['c1'])) / Decimal(str(terms[0]['term']))),
    })
result = {'status': 'evidence-only', 'source': str(source.relative_to(root)), 'rows': report}
out = Path(__file__).with_name('existing_terms_check.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
