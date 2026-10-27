#!/usr/bin/env python3
"""Variant family (NOT the round-8 twistU family): the exterior twist U_theta is put
only on the exterior bonds with longitudinal base coordinate < lo (the left half of the
exterior slab), so the right boundary of Omega_0 is untwisted.  At zero curvature the
first crossing is then a single boundary mode (no exponentially small left/right
splitting).  Computed in the q = 1 geometry with an arbitrary transverse Bloch phase
(as kscan.py).  Numerical evidence only; writes ./out/left_*.json."""
import sys
sys.dont_write_bytecode = True
from kscan import *   # noqa: F401,F403


class LeftFamily(Family):
    def angle(self, b, t=0):
        x, d = b
        y = self.shift(x, d)
        if not (self.in0(x) or self.in0(y)):
            return t if x[0] % self.nx < self.lo else 0
        return self.eps if x[0] == self.p and x[1] % 2 == 0 and x[2] % 2 == 0 and d == 1 else 0


def left_vacuum(R, ky, kz, dps, lo='0.45', hi='0.62', q=1, iy=None, iz=None):
    """q = 1 geometry with Bloch phase (ky, kz); or, if iy is given, the actual
    q-dilated geometry in character (iy, iz) (then ky, kz are only labels)."""
    mp.mp.dps = dps
    t_start = time.time()
    if iy is None:
        f = LeftFamily(1, R, mp.mpf(0), 0, 0, 1)
        f.ph = (mp.exp(2j * ky), mp.exp(2j * kz))
    else:
        f = LeftFamily(q, R, mp.mpf(0), iy, iz, 1)
    f.assemble()
    S = f.boundary_inverse()
    # Only the left boundary plaquettes are twisted, so the exterior part has the
    # affine pencil form Theta(t) = C + cos t A + sin t B (C from the right boundary);
    # recover C, A, B from t = 0, pi/2, pi and check the form at an independent angle.
    t0m = f.theta(0)
    t1m = f.theta(mp.pi / 2)
    t2m = f.theta(mp.pi)
    Cm = (t0m + t2m) / 2
    Am = (t0m - t2m) / 2
    Bm = t1m - Cm

    def theta(t):
        return Cm + mp.cos(t) * Am + mp.sin(t) * Bm
    tt = mp.mpf('0.3')
    pencil_err = mp.mnorm(f.theta(tt) - theta(tt), 1)

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
    T = 2 * (1 - mp.cos(ky)) + 2 * (1 - mp.cos(kz))
    rho = (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2
    row = dict(variant='left-only exterior twist', geometry_q=1, R=R, k=[ky, kz], dps=dps,
               rho=rho, vacuum_root=t, schur_low=[mp.re(e) for e in ev[:3]],
               next_schur_eigenvalue=ev[1], kernel_form_slope=slope, finite_sum_c1=c1,
               geometry=('q=1 with phase' if iy is None else f'actual q={q}, character ({iy},{iz})'),
               K=c1 / rho**(4 * q * R), pencil_identity_error=pencil_err,
               left_half_mass=sum(abs(x[i])**2 for i, j in enumerate(f.e)
                                  if f.bonds[j][0][0] < (f.lo + f.hi) / 2),
               seconds=time.time() - t_start)
    tag = f'{mp.nstr(ky, 6)}_{mp.nstr(kz, 6)}' if iy is None else f'q{q}_s{iy}_{iz}'
    fn = OUTDIR / f'left_R{R}_p{dps}_{tag}.json'
    fn.write_text(json.dumps(jsonable(row), indent=2) + '\n')
    print('LEFT', fn.name, 'root', mp.nstr(t, 16), 'next', mp.nstr(ev[1], 6),
          'slope', mp.nstr(slope, 8), 'c1', mp.nstr(c1, 12), 'K', mp.nstr(row['K'], 12),
          'lefthalf', mp.nstr(row['left_half_mass'], 6), 'pencil', mp.nstr(pencil_err, 3),
          'sec', round(time.time() - t_start), flush=True)
    return row


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--R', type=int, default=6)
    p.add_argument('--dps', type=int, default=50)
    p.add_argument('--ks', default='-pi/8')
    p.add_argument('--q', type=int, default=1)
    p.add_argument('--iy', type=int, default=None)
    p.add_argument('--iz', type=int, default=None)
    a = p.parse_args()
    if a.iy is not None:
        mp.mp.dps = a.dps
        my = a.iy if a.iy <= 2 * a.q else a.iy - 4 * a.q
        mz = a.iz if a.iz <= 2 * a.q else a.iz - 4 * a.q
        left_vacuum(a.R, mp.pi * my / (4 * a.q), mp.pi * mz / (4 * a.q), a.dps,
                    q=a.q, iy=a.iy, iz=a.iz)
        sys.exit(0)
    for ks in a.ks.split(','):
        mp.mp.dps = a.dps
        parts = ks.split(':')
        ky = mp.mpf(eval(parts[0].replace('pi', 'mp.pi')))
        kz = mp.mpf(eval(parts[-1].replace('pi', 'mp.pi')))
        left_vacuum(a.R, ky, kz, a.dps)
