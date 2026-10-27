#!/usr/bin/env python3
"""Which charged character crosses first at scale q, and its coefficient K.

Uses the q = 1 geometry with arbitrary transverse Bloch phases (see kscan.py): the
sector operator of scale q in the character with fine wave numbers (k_y, k_z) =
(pi m_y/(4q), pi m_z/(4q)) is, up to exponentially small Omega_1-length effects, the
q = 1 geometry operator with those phases.  For each candidate (m_y, m_z) near the
continuum minimiser it computes the vacuum crossing root; for the minimiser (and its
y<->z mirror) it also reports c1 and K = c1/rho^(4R).  Neutral sectors never cross on
(0, pi/2] (their exterior plaquette energy is cos(t)|curl|^2 >= 0), and higher bands
cross later; only the lowest charged band near (k*, k*) is scanned.
Numerical evidence only; writes ./out/first_q{q}_R{R}_p{dps}.json.
"""
import sys
sys.dont_write_bytecode = True
from kscan import *   # noqa: F401,F403


def root_only(R, ky, kz, dps, lo='0.45', hi='0.62'):
    mp.mp.dps = dps
    f = Family(1, R, mp.mpf(0), 0, 0, 1)
    f.ph = (mp.exp(2j * ky), mp.exp(2j * kz))
    f.assemble()
    S = f.boundary_inverse()
    th0 = f.theta(0)
    th1 = f.theta(mp.pi / 2)

    def low(t):
        return mp.eighe(S + mp.cos(t) * th0 + mp.sin(t) * th1, eigvals_only=True)[0]
    return mp.findroot(low, (mp.mpf(lo), mp.mpf(hi)), solver='secant',
                       tol=mp.power(10, -dps + 15), verify=False)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--q', type=int, required=True)
    p.add_argument('--R', type=int, default=6)
    p.add_argument('--dps', type=int, default=50)
    p.add_argument('--kstar', default='-0.267')
    p.add_argument('--width', type=int, default=1)
    a = p.parse_args()
    q = a.q
    mp.mp.dps = a.dps
    mstar = mp.mpf(a.kstar) * 4 * q / mp.pi
    mc = [int(mp.floor(mstar)) + d for d in range(-a.width + 1, a.width + 1)]
    rows = []
    for my in mc:
        for mz in mc:
            if mz < my:
                continue        # the vacuum is y<->z symmetric: roots agree
            ky = mp.pi * my / (4 * q)
            kz = mp.pi * mz / (4 * q)
            t = root_only(a.R, ky, kz, a.dps)
            rows.append(dict(m=[my, mz], k=[ky, kz], root=t))
            print('ROOT', q, my, mz, mp.nstr(t, 15), flush=True)
    rows.sort(key=lambda r: r['root'])
    best = rows[0]
    out = dict(q=q, R=a.R, dps=a.dps, candidates=rows, first=best['m'],
               gap_to_second=rows[1]['root'] - best['root'] if len(rows) > 1 else None)
    my, mz = best['m']
    out['first_sector'] = []
    for (y, z) in ([(my, mz)] if my == mz else [(my, mz), (mz, my)]):
        ky = mp.pi * y / (4 * q)
        kz = mp.pi * z / (4 * q)
        r = vacuum_at_phase(a.R, ky, a.dps, tag=f'q{q}_m{y}_{z}', kz=kz)
        out['first_sector'].append(dict(m=[y, z], c1=r['finite_sum_c1'], K=r['K'],
                                        slope=r['kernel_form_slope'],
                                        splitting=r['partner_splitting'],
                                        left_half_mass=r['left_half_mass']))
    fn = OUTDIR / f'first_q{q}_R{a.R}_p{a.dps}.json'
    fn.write_text(json.dumps(jsonable(out), indent=2) + '\n')
    print('FIRST', q, out['first'], 'gap', mp.nstr(out['gap_to_second'], 6),
          [(s['m'], mp.nstr(s['K'], 10)) for s in out['first_sector']], flush=True)
