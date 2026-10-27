#!/usr/bin/env python3
"""Half-space constant K(k) = c1 / rho_k^(4 R q) as a function of the transverse
wave number k, computed in the q = 1 geometry with an arbitrary diagonal Bloch phase.

The sector operator of the actual pinned assembly depends on the scale q only through
(i) the allowed Bloch phases exp(2 i k) per two-site translation (k = pi m/(4q)) and
(ii) the longitudinal lengths: left collar 2Rq, Omega_1 length (8R+8)q, right collar
2Rq.  The coefficient c1 sees the Omega_1 length only through exponentially small
tails.  Hence c1(q,R)/rho_k^(4qR) should be a function K(k) of k alone, computable in
the q = 1 geometry with radius R' (any R' large enough) and the phase exp(2 i k)
substituted for the character phase.  This script tests that claim against the
round-8 values (k = -pi/8: q = 2; k = -pi/16: q = 4) and scans k.

Imports the round-6 probe READ-ONLY (bytecode writing disabled); writes only to
./out.  Numerical evidence only.
"""
import sys
sys.dont_write_bytecode = True
PROBE = '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe'
sys.path.insert(0, PROBE)
from leading_source import *            # noqa: F401,F403  (probe + leading_h)
import resource
resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
HERE = Path(__file__).resolve().parent
OUTDIR = HERE / 'out'
OUTDIR.mkdir(exist_ok=True)


def rho_of(k):
    T = 4 * (1 - mp.cos(k))
    return (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2


def vacuum_at_phase(R, k, dps, lo='0.45', hi='0.62', tag='', kz=None):
    mp.mp.dps = dps
    t_start = time.time()
    f = Family(1, R, mp.mpf(0), 0, 0, 1)
    kz = k if kz is None else kz
    # phases per two-site transverse translation in y and z
    f.ph = (mp.exp(2j * k), mp.exp(2j * kz))
    f.assemble()
    S = f.boundary_inverse()
    th0 = f.theta(0)
    th1 = f.theta(mp.pi / 2)

    def theta(t):
        return mp.cos(t) * th0 + mp.sin(t) * th1

    def low(t, j=0):
        return mp.eighe(S + theta(t), eigvals_only=True)[j]
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
    # collar decay for transverse momentum (k, kz): 2 cosh kappa = 3 + T
    T = 2 * (1 - mp.cos(k)) + 2 * (1 - mp.cos(kz))
    rho = (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2
    row = dict(geometry_q=1, R=R, k=k, kz=kz, dps=dps, rho_k=rho, vacuum_root=t,
               vacuum_schur_low=[mp.re(e) for e in ev[:4]], partner_splitting=ev[1],
               kernel_form_slope=slope, finite_sum_c1=c1, K=c1 / rho**(4 * R),
               left_half_mass=sum(abs(x[i])**2 for i, j in enumerate(f.e)
                                  if f.bonds[j][0][0] < (f.lo + f.hi) / 2),
               positive_terms=sum(max(z, 0) for z in terms),
               negative_terms=sum(min(z, 0) for z in terms),
               seconds=time.time() - t_start,
               peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    fn = OUTDIR / f'kscan_R{R}_p{dps}_{tag or mp.nstr(k, 8)}.json'
    fn.write_text(json.dumps(jsonable(row), indent=2) + '\n')
    print('KSCAN', fn.name, 'k', mp.nstr(k, 10), mp.nstr(kz, 10), 'root', mp.nstr(t, 16),
          'split', mp.nstr(ev[1], 6), 'slope', mp.nstr(slope, 8),
          'c1', mp.nstr(c1, 12), 'K', mp.nstr(c1 / rho**(4 * R), 12),
          'sec', round(time.time() - t_start), flush=True)
    return row


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--R', type=int, default=18)
    p.add_argument('--dps', type=int, default=160)
    p.add_argument('--ks', default='-pi/8,-pi/16', help='comma-separated, e.g. "-pi/8,-pi/16"; '
                   'an entry "a:b" means (k_y, k_z) = (a, b)')
    a = p.parse_args()
    for ks in a.ks.split(','):
        mp.mp.dps = a.dps
        parts = ks.split(':')
        k = mp.mpf(eval(parts[0].replace('pi', 'mp.pi')))
        kz = mp.mpf(eval(parts[-1].replace('pi', 'mp.pi')))
        vacuum_at_phase(a.R, k, a.dps, tag=ks.replace('/', 'o').replace('*', 'x').replace(':', '_'), kz=kz)
