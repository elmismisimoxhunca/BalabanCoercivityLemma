#!/usr/bin/env python3
"""Vacuum data that control the small-curvature limit at fixed (q,R).

At eps = 0 the correction vanishes (round-6 limits: twistD_zero_amplitude).
For small eps the corrected crossing is shifted from the carrier crossing by
d(eps)/|slope| with d(eps) = c1*eps + O(eps^2), while the partner splitting
tends to its vacuum value s0 > 0.  Hence, if c1 != 0, the corrected crossing
lies strictly between consecutive carrier crossings (before the first one if
c1 > 0, after it if c1 < 0) for all small eps: a guarded separation either way.

This script computes, for one charged character, the vacuum first root t*,
the vacuum boundary Schur spectrum there (partner splitting s0), the slope of
the kernel Schur form, and the finite-sum coefficient
    c1 = 2 sum_j h'_j C2_j(W0 v0)
of round-6 leading_vacuum.py (h' from leading_source.leading_h, checked there
against the full KKT solve), generalised to any (q,R,character).
Imports the round-6 probe READ-ONLY.  Numerical evidence only.
"""
import sys
sys.dont_write_bytecode = True
PROBE = '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe'
sys.path.insert(0, PROBE)
from leading_source import *            # noqa: F401,F403  (probe + leading_h)
import resource
resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
HERE = Path(__file__).resolve().parent
OUTDIR = HERE / 'out'
OUTDIR.mkdir(exist_ok=True)


def run(q, R, dps, iy, iz, lo='0.5', hi='0.6'):
    mp.mp.dps = dps
    t_start = time.time()
    f = Family(q, R, mp.mpf(0), iy, iz, 1).assemble()
    S = f.boundary_inverse()
    th0 = f.theta(0)
    th1 = f.theta(mp.pi / 2)

    def theta(t):
        return mp.cos(t) * th0 + mp.sin(t) * th1

    def low(t, k=0):
        return mp.eighe(S + theta(t), eigvals_only=True)[k]
    t = mp.findroot(low, (mp.mpf(lo), mp.mpf(hi)), solver='secant',
                    tol=mp.power(10, -dps + 15), verify=False)
    ev, V = mp.eighe(S + theta(t))
    y = V[:, 0]
    rhs = S * y
    x = [sum(f.X[k][i] * rhs[k] for k in range(len(f.X))) for i in range(f.aug.n)]
    norm = mp.sqrt(sum(abs(z)**2 for z in x[:f.n]))
    x = [z / norm for z in x]
    w = f.dressed(x[:f.n], x[f.n:f.n + f.H.n])
    h = leading_h(f)
    c1, terms = f.correction(w, h)
    bv = mp.matrix([x[i] for i in f.boundary])
    step = mp.mpf(10)**(-20)
    slope = mp.re((bv.H * (theta(t + step) - theta(t - step)) * bv)[0] / (2 * step))
    row = dict(q=q, R=R, dps=dps, character=[iy, iz], vacuum_root=t,
               vacuum_schur_low=[mp.re(e) for e in ev[:4]],
               partner_splitting=ev[1], kernel_form_slope=slope,
               finite_sum_c1=c1,
               predicted_shift_per_eps=-c1 / slope,
               left_half_mass=sum(abs(x[i])**2 for i, j in enumerate(f.e)
                                  if f.bonds[j][0][0] < (f.lo + f.hi) / 2),
               positive_terms=sum(max(z, 0) for z in terms),
               negative_terms=sum(min(z, 0) for z in terms),
               seconds=time.time() - t_start,
               peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    fn = OUTDIR / f'vac_q{q}_R{R}_p{dps}_s{iy}_{iz}.json'
    fn.write_text(json.dumps(jsonable(row), indent=2) + '\n')
    print('VAC', fn, 'root', mp.nstr(t, 20), 'splitting', mp.nstr(ev[1], 10),
          'c1', mp.nstr(c1, 15), flush=True)
    return row


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--q', type=int, default=2)
    p.add_argument('--R', type=int, default=18)
    p.add_argument('--dps', type=int, default=340)
    p.add_argument('--iy', type=int, default=7)
    p.add_argument('--iz', type=int, default=7)
    p.add_argument('--lo', default='0.5')
    p.add_argument('--hi', default='0.6')
    a = p.parse_args()
    run(a.q, a.R, a.dps, a.iy, a.iz, a.lo, a.hi)
