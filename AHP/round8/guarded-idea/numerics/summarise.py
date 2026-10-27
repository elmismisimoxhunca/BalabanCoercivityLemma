#!/usr/bin/env python3
"""Markdown tables and SUMMARY.json from numerics/out/*.json (no new numerics)."""
import json, sys
from pathlib import Path
import mpmath as mp
mp.mp.dps = 1200
HERE = Path(__file__).resolve().parent
OUT = HERE / 'out'


def e(x, n=4):
    return mp.nstr(mp.mpf(x), n, min_fixed=0, max_fixed=0)


rows, summary = [], dict(separation=[], vacuum=[], screens=[])
for fn in sorted(OUT.glob('sep_q*_s*.json')):
    d = json.loads(fn.read_text())
    if int(d['R']) < 18:
        continue
    A = d['A_boundary_spectrum_at_tC1']
    C = d['C_boundary_spectrum_at_tC1']
    shift = mp.mpf(d['tC1_minus_tB1'])
    gap = mp.mpf(d['tB2_minus_tB1'])
    side = 'before (A PD)' if shift < 0 else 'after (A indefinite unit)'
    sep = (min(abs(mp.mpf(x)) for x in A) > 0 and abs(mp.mpf(C[0])) < mp.power(10, -int(d['dps']) + 60)
           and (shift < 0 or shift < gap))
    rows.append(f"| {d['q']} | {d['R']} | {d['epsilon']} | {d['dps']} | ({d['character'][0]},{d['character'][1]}) | "
                f"{e(d['unit_kernel_pairing'])} | {e(shift)} | {e(gap)} | {side} | "
                f"{e(A[0])}, {e(A[1])} | {e(C[0], 2)} | {e(d['corrected_kernel_augmented_residual'], 2)} | "
                f"{e(d['first_order_ratio'], 6)} | {'yes' if sep else 'NO'} |")
    summary['separation'].append(dict(file=fn.name, q=d['q'], R=d['R'], epsilon=d['epsilon'], dps=d['dps'],
                                      character=d['character'], pairing=d['unit_kernel_pairing'],
                                      shift=d['tC1_minus_tB1'], partner_gap=d['tB2_minus_tB1'],
                                      A_at_tC=A[:2], C_at_tC=C[0], separation=bool(sep)))
print('| q | R | eps | dps | char | <v,Dv> (unit v) | t_C1 - t_B1 | t_B2 - t_B1 | side | A at t_C1 (two lowest) | A-D at t_C1 | corr. kernel residual | exact/first-order | separation |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
print('\n'.join(rows))
vrows = []
for fn in sorted(OUT.glob('vac_q*.json')):
    d = json.loads(fn.read_text())
    vrows.append(f"| {d['q']} | {d['R']} | {d['dps']} | ({d['character'][0]},{d['character'][1]}) | {e(d['vacuum_root'], 16)} | "
                 f"{e(d['partner_splitting'])} | {e(d['kernel_form_slope'])} | {e(d['finite_sum_c1'])} | "
                 f"{e(d['left_half_mass'], 6)} |")
    summary['vacuum'].append(dict(file=fn.name, q=d['q'], R=d['R'], dps=d['dps'], character=d['character'],
                                  root=d['vacuum_root'], splitting=d['partner_splitting'],
                                  slope=d['kernel_form_slope'], c1=d['finite_sum_c1']))
if vrows:
    print()
    print('| q | R | dps | char | vacuum root t* | partner splitting s0 | kernel-form slope | c1 | left-half mass |')
    print('|---|---|---|---|---|---|---|---|---|')
    print('\n'.join(vrows))
for fn in sorted(OUT.glob('screen_q*.json')):
    d = json.loads(fn.read_text())
    secs = d['sectors']
    neg = [(s['charge'], s['character'], s['schur_min_at_angles']) for s in secs if min(s['schur_min_at_angles']) <= 0]
    pos = [s for s in secs if min(s['schur_min_at_angles']) > 0]
    summary['screens'].append(dict(file=fn.name, complete=d.get('complete', False), sectors=len(secs),
                                   B_inertia_ok_all=all(s['B_inertia_ok'] for s in secs),
                                   angles=d['angles'], nonpositive=neg,
                                   min_positive=min((min(s['schur_min_at_angles']) for s in pos), default=None),
                                   min_at_0=min(s['schur_min_at_0'] for s in secs)))
    print(f"\nscreen {fn.name}: complete={d.get('complete')} sectors={len(secs)} B-inertia-ok-all={all(s['B_inertia_ok'] for s in secs)} "
          f"angles={d['angles']} nonpositive={neg} min over the rest={summary['screens'][-1]['min_positive']}")
(HERE / 'SUMMARY.json').write_text(json.dumps(summary, indent=1) + '\n')
