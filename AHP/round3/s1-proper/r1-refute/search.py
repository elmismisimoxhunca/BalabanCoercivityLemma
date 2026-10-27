#!/usr/bin/env python3
"""Bounded Cartan-sector diagnostic, NOT a full-form simulation.

Operator/source dictionary (current frozen files):
* periodic plaquette edges/corner selector: pin/Statement.lean:30,40,43.
* Zb, Uth: lean/src/D1Path.lean:25,46 (theta only on non-touching bonds).
* scalar Cartan Delta pairing: lean/src/CvO23.lean:162
  inner_deltaKLocCLM_sigma3; actual DeltaS: lean/src/D1Lit.lean:39.
* singleton field: lean/src/D1Eval2.lean:29.
* curlValueCovariant: lean/src/AdalyFormal/Balaban/CovariantOperators.lean:315
  (the source line is also checked and recorded in search.json).
We do NOT model W, J, mass, Q, C, or any inverse. We test the local
support identity needed to transfer the actual carrier theorem in Lean.
No admissibility/class certification is claimed by this small-torus scan.
"""
import itertools
import json
import math
from pathlib import Path
import random
import resource

resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).with_name('search.json')

def run(n, shape):
    sites = list(itertools.product(range(n), repeat=3))
    def shift(x, d):
        y = list(x)
        y[d] = (y[d] + 1) % n
        return tuple(y)
    def inside(x):
        if shape == 'slab':
            return x[0] < n//2
        return x[0] < n//2 and x[1] < n//2
    bonds = [(x, d) for x in sites for d in range(3)]
    touch = {b: inside(b[0]) or inside(shift(*b)) for b in bonds}
    plaqs = []
    one_corner = 0
    unread = set()
    for x in sites:
        for mu, nu in [(0, 1), (0, 2), (1, 2)]:
            y, z = shift(x, mu), shift(x, nu)
            corners = (x, y, z, shift(y, nu))
            edges = ((x, mu), (y, nu), (z, mu), (x, nu))
            count = sum(inside(v) for v in corners)
            one_corner += count == 1
            if count:
                unread.update(e for e in edges if not touch[e])
            plaqs.append((edges, count))
    rng = random.Random(1729 + n)
    supported = {e: rng.uniform(-1, 1) if touch[e] else 0.0 for e in bonds}
    singleton = {e: float(e == ((n//2-1, 0, 0), 0)) for e in bonds}
    rows = []
    for theta in [0, math.pi/4, math.pi/2, 3*math.pi/4, math.pi]:
        phase = {e: 0.0 if touch[e] else theta for e in bonds}
        def form(field, selector):
            ans = 0.0
            for (a,b,c,d), count in plaqs:
                if selector == 'corner' and count == 0:
                    continue
                if selector == 'inside' and count != 4:
                    continue
                curvature = phase[a]+phase[b]-phase[c]-phase[d]
                curl = field[a]+field[b]-field[c]-field[d]
                ans += math.cos(curvature)*curl*curl
            return ans
        all_q, corner_q = form(supported, 'all'), form(supported, 'corner')
        q_single = form(singleton, 'corner')
        assert abs(all_q-corner_q) < 1e-10
        if shape == 'slab':
            assert abs(q_single-4*math.cos(theta)) < 1e-10
        rows.append({'theta': theta, 'singleton_corner': q_single,
                     'singleton_inside': form(singleton, 'inside'),
                     'random_touching_all': all_q, 'random_touching_corner': corner_q,
                     'all_corner_gap': all_q-corner_q})
    assert max(abs(phase[e]) for e in bonds if touch[e]) == 0
    return {'side': n, 'shape': shape, 'one_corner_plaquettes': one_corner,
            'corner_read_non_touching_bonds': len(unread), 'rows': rows}

source = ROOT/'lean/src/AdalyFormal/Balaban/CovariantOperators.lean'
locs = [i for i, line in enumerate(source.read_text().splitlines(), 1)
        if 'def curlValueCovariant' in line]
result = {'status': 'diagnostic only; no headline claim',
          'curl_source': str(source.relative_to(ROOT)), 'curl_lines': locs,
          'memory_cap_bytes': 1024**3,
          'experiments': [run(n, shape) for n in (4, 6, 8, 16)
                          for shape in ('slab', 'corner_box')]}
result['peak_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
OUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'output': str(OUT), 'peak_rss_kib': result['peak_rss_kib'],
                  'max_pairing_gap': max(abs(r['all_corner_gap'])
                    for e in result['experiments'] for r in e['rows']),
                  'slab_pi_values': [e['rows'][-1]['singleton_corner']
                    for e in result['experiments'] if e['shape']=='slab']}, indent=2))
