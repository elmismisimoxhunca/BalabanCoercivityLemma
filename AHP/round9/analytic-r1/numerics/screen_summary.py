#!/usr/bin/env python3
"""Summarise the left-twist all-character screens (no new numerics).  Writes SCREEN_Q4.md
(covering q = 2 and, if present, q = 4)."""
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
lines = ['# Left-twist all-character vacuum screens (double-precision spectra; a screen, not a certificate)', '']
for q, R in [(2, 18), (4, 18)]:
    p = HERE / 'out' / f'screen_left_q{q}_R{R}_vacuum.json'
    if not p.exists():
        lines.append(f'q={q}, R={R}: no output file.')
        continue
    d = json.loads(p.read_text())
    n = len(d['sectors'])
    lines.append(f"## q={q}, R={R}: {n} of {2 * (4 * q) ** 2} sectors, complete={d.get('complete', False)}, "
                 f"{round(d['seconds'])} s, angles {d['angles']}")
    bad = [s for s in d['sectors'] if not s['B_inertia_ok']]
    lines.append(f"- B inertia failures: {len(bad)}")
    lines.append(f"- min boundary Schur eigenvalue at t=0 over all sectors: {min(s['schur_min_at_0'] for s in d['sectors']):.12g}")
    rows = sorted(d['sectors'], key=lambda s: s['schur_min_at_angles'][1])
    lines.append('- lowest sectors at the middle angle (charge, character, minima at [0] + angles):')
    for s in rows[:6]:
        lines.append(f"  - {s['charge']} {tuple(s['character'])}: "
                     + ', '.join(f'{x:.6g}' for x in [s['schur_min_at_0']] + s['schur_min_at_angles']))
    lines.append('')
(HERE / 'SCREEN_Q4.md').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
