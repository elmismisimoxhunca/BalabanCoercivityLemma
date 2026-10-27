#!/usr/bin/env python3
"""Compare the first-order window of `perturbative_sign_change` with round-8 data.

Reads (read-only) the round-8 vacuum files vac_q*_R*_p*_s*.json (vacuum root t*,
kernel-form slope sigma, finite-sum coefficient c1, partner splitting) and the exact
corrected-Schur separation files sep_q*_R*_e*_p*_s*.json (t_C1 - t_B1).  For every
separation run inside the small-curvature window it prints
  predicted shift  eps*|c1|/|sigma|   (the distance between the corrected and the
                                       carrier crossing used by the theorem's window)
  measured shift   t_C1 - t_B1        (exact boundary Schur computation, round 8)
  side             sign of c1 (pre-crossing if c1 > 0, post-crossing if c1 < 0)
No new spectral computation is done here.  Numerical evidence only.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
SRC = Path('/home/sebastian/BalabanCoercivityLemma/AHP/round8/guarded-idea/numerics/out')


def num(x):
    return mp.mpf(x) if isinstance(x, str) else mp.mpf(x)


def main():
    vac = {}
    for fn in sorted(SRC.glob('vac_q*_R*_p*_s*.json')):
        d = json.loads(fn.read_text())
        vac[(d['q'], d['R'])] = d
    rows = []
    for fn in sorted(SRC.glob('sep_q*_R*_e*_p*_s*.json')):
        d = json.loads(fn.read_text())
        key = (d['q'], d['R'])
        if key not in vac:
            continue
        v = vac[key]
        eps = num(d['epsilon'])
        c1 = num(v['finite_sum_c1'])
        sigma = num(v['kernel_form_slope'])
        gap = num(v['partner_splitting'])
        pred = eps * abs(c1) / abs(sigma)
        meas = num(d['tC1_minus_tB1'])
        partner = num(d['tB2_minus_tB1'])
        rows.append(dict(file=fn.name, q=d['q'], R=d['R'], eps=d['epsilon'],
                         c1=mp.nstr(c1, 8), sigma=mp.nstr(sigma, 8),
                         vacuum_partner_splitting=mp.nstr(gap, 6),
                         predicted_abs_shift=mp.nstr(pred, 10),
                         measured_shift=mp.nstr(meas, 10),
                         ratio=mp.nstr(abs(meas) / pred, 12),
                         side='post-crossing' if c1 < 0 else 'pre-crossing',
                         measured_side='post-crossing' if meas > 0 else 'pre-crossing',
                         shift_over_partner_gap=mp.nstr(abs(meas) / partner, 6)))
    out = Path(__file__).resolve().parent / 'prediction_check.json'
    out.write_text(json.dumps(rows, indent=2) + '\n')
    for r in rows:
        print(r['q'], r['R'], r['eps'], r['side'], r['measured_side'],
              'pred', r['predicted_abs_shift'], 'meas', r['measured_shift'],
              'ratio', r['ratio'], 'shift/partner', r['shift_over_partner_gap'])
    return 0


if __name__ == '__main__':
    sys.exit(main())
