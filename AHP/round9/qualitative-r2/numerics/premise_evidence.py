#!/usr/bin/env python3
"""Numerical evidence for the reduced premise of round 9.2 (evidence only; proves nothing).

Reads, read-only, the round-8 vacuum and screen outputs and the round-9.1 reflected
separation run, and tabulates, for each computed (q, R):
  * the canonical forward crossing: the vacuum root of the first character, and whether the
    all-sector screen at that angle has no other non-positive sector (so the end of the
    initial positive semidefinite interval of the full carrier is this crossing);
  * the partner splitting at the crossing (positive: the canonical kernel is one complex
    charged line, and the next crossing is a positive distance away);
  * the vacuum coupling c1 = <u0, De u0>/|u0|^2 on that line (CanonicalCoupling holds with
    the negative sign; by the compiled gauge flip it is positive on the backward kernel);
  * the round-9.1 reflected run, which by the compiled gauge flip is the literal family at
    negative angle: corrected crossing before the carrier crossing, carrier positive definite.
Writes premise_evidence.json and premise_evidence.md next to this script.
"""
import json
import sys
from pathlib import Path

import mpmath

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
AHP = HERE.parents[2]
R8 = AHP / 'round8/guarded-idea/numerics/out'
R91 = AHP / 'round9/qualitative-r1/numerics/out'

VAC = [('vac_q2_R18_p340_s7_7.json', 'screen_q2_R18_vacuum.json'),
       ('vac_q2_R20_p400_s7_7.json', None),
       ('vac_q2_R24_p400_s7_7.json', None),
       ('vac_q2_R30_p400_s7_7.json', None),
       ('vac_q4_R18_p520_s15_15.json', 'screen_q4_R18_vacuum.json')]


def short(x, n=6):
    try:
        return mpmath.nstr(mpmath.mpf(str(x)), n)
    except (TypeError, ValueError):
        return str(x)


def screen_summary(name, char):
    d = json.loads((R8 / name).read_text())
    rows = []
    for s in d['sectors']:
        vals = [float(v) for v in s['schur_min_at_angles']]
        rows.append((min(vals), tuple(s['character']), s['charge'], s['B_inertia_ok']))
    rows.sort()
    nonpos = [r for r in rows if r[0] <= 1e-6]
    others = [r for r in rows if not (r[1] == tuple(char) and r[2] == 1)]
    return {
        'angles': d['angles'],
        'sectors': len(rows),
        'B_inertia_ok_all': all(r[3] for r in rows),
        'nonpositive_sectors': [[list(r[1]), r[2], r[0]] for r in nonpos],
        'min_other_sector': others[0][0] if others else None,
        'precision': d['screening_precision'],
    }


out = []
for vac, scr in VAC:
    v = json.loads((R8 / vac).read_text())
    row = {
        'q': int(v['q']), 'R': int(v['R']), 'dps': int(v['dps']),
        'character': v['character'],
        'vacuum_root': v['vacuum_root'],
        'partner_splitting': v['partner_splitting'],
        'kernel_form_slope': v['kernel_form_slope'],
        'c1': v['finite_sum_c1'],
        'c1_positive_terms': v['positive_terms'],
        'c1_negative_terms': v['negative_terms'],
        'source': str((R8 / vac).relative_to(AHP.parent)),
    }
    if scr:
        row['screen'] = screen_summary(scr, v['character'])
        row['screen_source'] = str((R8 / scr).relative_to(AHP.parent))
    out.append(row)

refl = json.loads((R91 / 'sep_q2_R18_e-1e-100_p400_s7_7_reflected.json').read_text())
reflected = {
    'curvature': refl['epsilon'],
    'tC1_minus_tB1': refl['tC1_minus_tB1'],
    'tB2_minus_tB1': refl['tB2_minus_tB1'],
    'A_boundary_spectrum_at_tC1': refl['A_boundary_spectrum_at_tC1'][:3],
    'A_negative_count_at_tC1': refl['A_negative_count_at_tC1'],
    'C_boundary_spectrum_at_tC1': refl['C_boundary_spectrum_at_tC1'][:2],
    'unit_kernel_pairing': refl['unit_kernel_pairing'],
    'source': str((R91 / 'sep_q2_R18_e-1e-100_p400_s7_7_reflected.json').relative_to(AHP.parent)),
}
res = {'vacuum': out, 'reflected_q2_R18': reflected,
       'note': 'floating point (mpmath) evidence from earlier rounds; no certificates'}
(HERE / 'premise_evidence.json').write_text(json.dumps(res, indent=2) + '\n')

md = ['| q | R | char | canonical root t* | partner splitting | c1 | other sectors at t* |',
      '|---|---|---|---|---|---|---|']
for r in out:
    sc = r.get('screen')
    other = (f"min {short(sc['min_other_sector'], 4)} ({sc['sectors']} sectors, "
             f"{sc['precision']})" if sc else 'not screened')
    md.append(f"| {r['q']} | {r['R']} | {tuple(r['character'])} | {short(r['vacuum_root'], 13)} | "
              f"{short(r['partner_splitting'], 4)} | {short(r['c1'], 6)} | {other} |")
md.append('')
md.append('Reflected run (q=2, R=18, curvature -1e-100; by the gauge flip this is the literal '
          'family at negative angle): '
          f"t_C1 - t_B1 = {short(reflected['tC1_minus_tB1'], 7)}, carrier boundary spectrum at "
          f"t_C1 = {[short(x, 4) for x in reflected['A_boundary_spectrum_at_tC1']]}, "
          f"corrected lowest = {short(reflected['C_boundary_spectrum_at_tC1'][0], 3)}, "
          f"pairing = {short(reflected['unit_kernel_pairing'], 7)}.")
(HERE / 'premise_evidence.md').write_text('\n'.join(md) + '\n')
print('\n'.join(md))
