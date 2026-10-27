#!/usr/bin/env python3
"""Tables for NOTES.md from ./out/*.json (no new numerics).  Writes tables.md, SUMMARY.json."""
import json, glob
from pathlib import Path
import mpmath as mp
mp.mp.dps = 30
HERE = Path(__file__).resolve().parent
O = HERE / 'out'
def L(p): return json.loads((O / p).read_text())
def n(x, d=10): return mp.nstr(mp.mpf(x), d)
lines = []
summary = {}
# 1. dictionary checks
lines.append('### Dictionary: actual q-dilated family vs. q = 1 geometry with the same Bloch phase\n')
lines.append('| run | geometry | k | vacuum root | slope | K = c1/rho^(4qR) | left-half mass |')
lines.append('|---|---|---|---|---|---|---|')
rows = []
for p, geo in [('actual_q2_R2_p50_s7_7.json', 'actual q=2, R=2, (7,7)'),
               ('kscan_R4_p30_-pio8.json', 'q=1 geometry, R=4, phase k'),
               ('actual_q4_R2_p60_s15_15.json', 'actual q=4, R=2, (15,15)'),
               ('kscan_R6_p40_-pio16.json', 'q=1 geometry, R=6, phase k'),
               ('kscan_R16_p80_-pix3o32.json', 'q=1 geometry, R=16, phase k'),
               ('actual_q8_R2_p80_s29_29.json', 'actual q=8, R=2, (29,29), 80 digits'),
               ('actual_q8_R2_p80_s28_28.json', 'actual q=8, R=2, (28,28), 80 digits')]:
    d = L(p)
    k = d['k'][0] if isinstance(d['k'], list) else d['k']
    lh = d.get('left_half_mass', '0.5')
    lines.append(f"| {p} | {geo} | {n(k, 8)} | {n(d['vacuum_root'], 16)} | {n(d['kernel_form_slope'], 8)} | {n(d['K'], 12)} | {n(lh, 6)} |")
    rows.append(dict(file=p, geometry=geo, k=k, root=d['vacuum_root'], K=d['K'], left_half=lh))
summary['dictionary'] = rows
# 2. K along the diagonal (symmetric twist, balanced kernel) and left twist
lines.append('\n### K(k) on the diagonal k_y = k_z = k (q = 1 geometry, R = 6)\n')
lines.append('| k | vacuum root t(k) | slope | K (round-8 twist) | K_L (left twist) |')
lines.append('|---|---|---|---|---|')
sym = {}
for p in glob.glob(str(O / 'kscan_R6_p*.json')):
    d = json.loads(Path(p).read_text())
    if 'kz' in d and mp.mpf(d['kz']) != mp.mpf(d['k']):
        continue
    sym[round(float(d['k']), 6)] = d
left = {}
for p in glob.glob(str(O / 'left_R6_p50_*.json')):
    d = json.loads(Path(p).read_text())
    left[round(float(d['k'][0]), 6)] = d
krow = []
for k in sorted(sym):
    d = sym[k]
    kl = left.get(k)
    lines.append(f"| {n(d['k'], 8)} | {n(d['vacuum_root'], 14)} | {n(d['kernel_form_slope'], 8)} | {n(d['K'], 10)} | {n(kl['K'], 10) if kl else ''} |")
    krow.append(dict(k=d['k'], root=d['vacuum_root'], K=d['K'], K_left=kl['K'] if kl else None))
summary['K_diagonal'] = krow
# 3. off-diagonal
lines.append('\n### Off-diagonal momenta (q = 1 geometry, R = 6; the defect breaks y<->z)\n')
lines.append('| (k_y, k_z) | root | K |')
lines.append('|---|---|---|')
for p in sorted(glob.glob(str(O / 'kscan_R6_p50_*_*.json'))):
    d = json.loads(Path(p).read_text())
    if 'kz' in d and mp.mpf(d['kz']) != mp.mpf(d['k']):
        lines.append(f"| ({n(d['k'], 6)}, {n(d['kz'], 6)}) | {n(d['vacuum_root'], 14)} | {n(d['K'], 10)} |")
# 4. first sector per scale
lines.append('\n### First crossing character at scale q (diagonal candidates and neighbours scanned)\n')
lines.append('| q | first (m_y, m_z) | k = pi m/(4q) | root | gap to next candidate root | K at first sector |')
lines.append('|---|---|---|---|---|---|')
fs = []
for q in [2, 4, 8, 16, 32, 64, 128, 256]:
    d = L(f'first_q{q}_R6_p50.json')
    m = d['first']
    best = [c for c in d['candidates'] if c['m'] == m][0]
    K = d['first_sector'][0]['K']
    lines.append(f"| {q} | ({m[0]}, {m[1]}) | {n(best['k'][0], 8)} | {n(best['root'], 14)} | {n(d['gap_to_second'], 4)} | {n(K, 10)} |")
    fs.append(dict(q=q, first=m, k=best['k'][0], root=best['root'], gap=d['gap_to_second'], K=K))
summary['first_sector'] = fs
# 5. R independence
lines.append('\n### R-independence of K at k = -pi/8 (q = 1 geometry)\n')
lines.append('| R | dps | K |')
lines.append('|---|---|---|')
for p, R, dps in [('kscan_R4_p30_-pio8.json', 4, 30), ('kscan_R6_p40_-pio8.json', 6, 40),
                  ('kscan_R8_p60_-pio8.json', 8, 60), ('kscan_R10_p70_-pio8.json', 10, 70)]:
    lines.append(f"| {R} | {dps} | {n(L(p)['K'], 15)} |")
lines.append('| round 8, actual q=2, R=18..30 | 340-400 | -0.0191639341944987 |')
# 6. left twist on actual geometries
lines.append('\n### Left-only twist on the actual geometries (50 digits)\n')
lines.append('| run | root | next Schur eigenvalue | slope | c1 | K_L | left-half mass |')
lines.append('|---|---|---|---|---|---|---|')
for p in ['left_R2_p50_q2_s7_7.json', 'left_R2_p50_q4_s15_15.json', 'left_R2_p50_q8_s29_29.json']:
    d = L(p)
    lines.append(f"| {p} | {n(d['vacuum_root'], 16)} | {n(d['next_schur_eigenvalue'], 6)} | {n(d['kernel_form_slope'], 8)} | {n(d['finite_sum_c1'], 10)} | {n(d['K'], 12)} | {n(d['left_half_mass'], 4)} |")
# 7. terms
lines.append('\n### Structure of c1 = 2 sum_j h_j C2_j (left twist, q = 1 geometry, R = 8): share of c1 per coarse bond j of Omega_1\n')
T = L('terms_left_R8_p50.json')
lines.append('| k | K_L | j=0 | j=1 | j=2 | j=3 |')
lines.append('|---|---|---|---|---|---|')
for r in T:
    sh = [t['share'] for t in r['terms'][:4]]
    lines.append(f"| {n(r['k'], 8)} | {n(r['K_L'], 10)} | " + ' | '.join(n(s, 6) for s in sh) + ' |')
(HERE / 'tables.md').write_text('\n'.join(lines) + '\n')
(HERE / 'SUMMARY.json').write_text(json.dumps(summary, indent=2, default=str) + '\n')
print('\n'.join(lines))
