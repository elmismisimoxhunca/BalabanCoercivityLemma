#!/usr/bin/env python3
"""Dictionary check: the actual q-dilated family (round-6 probe Family(q, R) with its
own character phases) versus the q = 1 geometry with the same Bloch phase (kscan.py).
Prints the vacuum root, slope, splitting, c1 and K = c1/rho^(4qR) of the actual family
in character (iy, iz).  Numerical evidence only; writes ./out/actual_*.json."""
import sys
sys.dont_write_bytecode = True
from kscan import *   # noqa: F401,F403


def actual(q, R, iy, iz, dps, lo='0.45', hi='0.62'):
    mp.mp.dps = dps
    t_start = time.time()
    f = Family(q, R, mp.mpf(0), iy, iz, 1).assemble()
    S = f.boundary_inverse()
    th0 = f.theta(0)
    th1 = f.theta(mp.pi / 2)

    def theta(t):
        return mp.cos(t) * th0 + mp.sin(t) * th1

    def low(t):
        return mp.eighe(S + theta(t), eigvals_only=True)[0]
    t = mp.findroot(low, (mp.mpf(lo), mp.mpf(hi)), solver='secant',
                    tol=mp.power(10, -dps + 15), verify=False)
    ev, V = mp.eighe(S + theta(t))
    y = V[:, 0]
    rhs = S * y
    x = [sum(f.X[j][i] * rhs[j] for j in range(len(f.X))) for i in range(f.aug.n)]
    norm = mp.sqrt(sum(abs(z)**2 for z in x[:f.n]))
    x = [z / norm for z in x]
    w = f.dressed(x[:f.n], x[f.n:f.n + f.H.n])
    h = leading_h(f)
    c1, terms = f.correction(w, h)
    bv = mp.matrix([x[i] for i in f.boundary])
    step = mp.mpf(10)**(-20)
    slope = mp.re((bv.H * (theta(t + step) - theta(t - step)) * bv)[0] / (2 * step))
    my = iy if iy <= 2 * q else iy - 4 * q
    mz = iz if iz <= 2 * q else iz - 4 * q
    ky = mp.pi * my / (4 * q)
    kz = mp.pi * mz / (4 * q)
    T = 2 * (1 - mp.cos(ky)) + 2 * (1 - mp.cos(kz))
    rho = (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2
    row = dict(q=q, R=R, character=[iy, iz], k=[ky, kz], dps=dps, rho=rho, vacuum_root=t,
               partner_splitting=ev[1], kernel_form_slope=slope, finite_sum_c1=c1,
               K=c1 / rho**(4 * q * R),
               left_half_mass=sum(abs(x[i])**2 for i, j in enumerate(f.e)
                                  if f.bonds[j][0][0] < (f.lo + f.hi) / 2),
               schur_low=[mp.re(e) for e in ev[:3]],
               positive_terms=sum(max(z, 0) for z in terms),
               negative_terms=sum(min(z, 0) for z in terms),
               seconds=time.time() - t_start,
               peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    fn = OUTDIR / f'actual_q{q}_R{R}_p{dps}_s{iy}_{iz}.json'
    fn.write_text(json.dumps(jsonable(row), indent=2) + '\n')
    print('ACTUAL', fn.name, 'root', mp.nstr(t, 16), 'split', mp.nstr(ev[1], 6),
          'slope', mp.nstr(slope, 8), 'c1', mp.nstr(c1, 12), 'K', mp.nstr(row['K'], 12),
          'lefthalf', mp.nstr(row['left_half_mass'], 8),
          'pos', mp.nstr(row['positive_terms'], 6), 'neg', mp.nstr(row['negative_terms'], 6),
          'sec', round(time.time() - t_start), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--q', type=int, required=True)
    p.add_argument('--R', type=int, required=True)
    p.add_argument('--iy', type=int, required=True)
    p.add_argument('--iz', type=int, required=True)
    p.add_argument('--dps', type=int, default=60)
    a = p.parse_args()
    actual(a.q, a.R, a.iy, a.iz, a.dps)
