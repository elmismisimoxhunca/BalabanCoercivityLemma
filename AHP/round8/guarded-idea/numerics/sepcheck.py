#!/usr/bin/env python3
"""Sign-free separation check on the round-6 curved twist family.

Imports the round-6 probe transcription READ-ONLY (operator dictionary:
AHP/round6/probe/SOURCES.md).  Nothing is written outside this directory;
in particular probe.run() and positivity.initial() (which write into the
probe directory) are never called.

For one transverse character it computes, at working precision:
  S   = (E_b* B^-1 E_b)^-1                boundary Schur of localized B
  S_C = (E_b* (B-D)^-1 E_b)^-1            the same for C = B - D, using the
                                          exact corrected augmented system
                                          positivity.corrected_aug
  theta(t)                                omitted-plaquette Hessian on the
                                          boundary coordinates (exterior Uth)
With B, C positive definite (screened separately), the carrier A(t) and the
corrected carrier A(t)-D have the inertia of S+theta(t), S_C+theta(t)
respectively (Schur complement / congruence), in this character.

It locates the first two roots of A (t_B1, t_B2) and of A-D (t_C1, t_C2) and
evaluates both boundary spectra at t_C1 and on a short interval.  Numerical
evidence only: no interval arithmetic, no certified enclosure.
"""
import os, sys
sys.dont_write_bytecode = True
PROBE = '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe'
sys.path.insert(0, PROBE)
from probe import *                      # noqa: F401,F403  (sets RLIMIT_AS 7 GiB)
from positivity import draw, corrected_aug
import resource
resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
HERE = Path(__file__).resolve().parent
OUTDIR = HERE / 'out'
OUTDIR.mkdir(exist_ok=True)


def boundary_schur(f, aug):
    solver = Refine(aug)
    X = []
    for k, i in enumerate(f.boundary):
        rhs = [0] * aug.n
        rhs[i] = 1
        X.append(solver.solve(rhs))
    Cm = mp.matrix([[col[i] for col in X] for i in f.boundary])
    Cm = (Cm + Cm.H) / 2
    return Cm**-1, X


def eigs(M):
    ev, V = mp.eighe(M)
    return [mp.re(x) for x in ev], V


def lam(M, k=0):
    return eigs(M)[0][k]


def carrier_lift(f, S, X, y):
    rho = S * y
    full = [sum(X[k][i] * rho[k] for k in range(len(X))) for i in range(len(X[0]))]
    nrm = mp.sqrt(sum(abs(v)**2 for v in full[:f.n]))
    return [x / nrm for x in full], nrm


def run(q, R, estr, dps, iy, iz, tag=''):
    mp.mp.dps = dps
    eps = mp.mpf(estr)
    t_start = time.time()
    f = Family(q, R, eps, iy, iz, 1).assemble()
    S, X = boundary_schur(f, f.aug)
    print('S done', time.time() - t_start, flush=True)
    nf = Family(q, R, eps, 0, 0, 0).assemble()
    hj, hres = nf.hj()
    D, jet_check = draw(f, hj)
    ca = corrected_aug(f, D)
    SC, XC = boundary_schur(f, ca)
    print('S_C done', time.time() - t_start, flush=True)
    th0 = f.theta(0)
    th1 = f.theta(mp.pi / 2)

    def theta(t):
        return mp.cos(t) * th0 + mp.sin(t) * th1
    # exterior pencil identity (path_identity.py) re-checked on this run
    pencil_err = max(abs(x) for x in (f.theta(mp.mpf('0.57')) - theta(mp.mpf('0.57'))))
    tol = mp.power(10, -dps + 20)

    def root(M, k, a, b):
        return mp.findroot(lambda t: lam(M + theta(t), k), (a, b), solver='secant',
                           tol=tol, verify=False)
    tB1 = root(S, 0, mp.mpf('0.5'), mp.mpf('0.7'))
    evB, VB = eigs(S + theta(tB1))
    # first corrected root: start the secant at tB1 and a step set by the
    # first-order shift; the bracket is checked afterwards, not assumed.
    gC = lam(SC + theta(tB1))
    h = mp.mpf(10)**(-30)
    slope = (lam(SC + theta(tB1 + h)) - lam(SC + theta(tB1 - h))) / (2 * h)
    tC1 = root(SC, 0, tB1, tB1 - 2 * gC / slope)
    # second roots (the near-degenerate partner mode)
    g2 = evB[1]
    s2 = (lam(S + theta(tB1 + h), 1) - lam(S + theta(tB1 - h), 1)) / (2 * h)
    tB2 = root(S, 1, tB1 - g2 / s2 * mp.mpf('0.9'), tB1 - g2 / s2 * mp.mpf('1.1'))
    gC2 = lam(SC + theta(tC1), 1)
    sC2 = (lam(SC + theta(tC1 + h), 1) - lam(SC + theta(tC1 - h), 1)) / (2 * h)
    tC2 = root(SC, 1, tC1 - gC2 / sC2 * mp.mpf('0.9'), tC1 - gC2 / sC2 * mp.mpf('1.1'))
    # spectra at the corrected crossing
    evA_tC, VA_tC = eigs(S + theta(tC1))
    evC_tC, VC_tC = eigs(SC + theta(tC1))
    evC_tB, _ = eigs(SC + theta(tB1))
    evA_0, _ = eigs(S + th0)
    evC_0, _ = eigs(SC + th0)
    # interval [t0,t1] on the far side of tB1 from nothing: t0,t1 between
    # the A-roots, chosen around tC1 (works for either sign of tC1-tB1)
    dlt = tC1 - tB1
    t0 = tB1 + dlt / 10 if dlt > 0 else tB1 + 2 * dlt
    t1 = tB1 + 2 * dlt if dlt > 0 else tB1 + dlt / 10
    ivl = []
    for t in [t0, (t0 + t1) / 2, t1]:
        ea = eigs(S + theta(t))[0]
        ec = eigs(SC + theta(t))[0]
        ivl.append(dict(t_minus_tB1=t - tB1, A_low=ea[:3], C_low=ec[:3],
                        A_negative=sum(1 for x in ea if x < 0),
                        C_negative=sum(1 for x in ec if x < 0)))
    # first-order consistency: <y,(S_C-S)y> = -|v|^2 <v^,D v^> + O(D^2)
    y = VB[:, 0]
    full, nrm = carrier_lift(f, S, X, y)
    v = full[:f.n]
    u = full[f.n:f.n + f.H.n]
    pairing, _ = f.correction(f.dressed(v, u), hj)
    first_order = mp.re((y.H * (SC - S) * y)[0])
    # kernel of A-D at tC1: residual in the corrected augmented system
    yc = VC_tC[:, 0]
    fullc, _ = carrier_lift(f, SC, XC, yc)
    resid = ca.apply(fullc)
    thc = theta(tC1)
    bvc = mp.matrix([fullc[i] for i in f.boundary])
    tv = thc * bvc
    for k, i in enumerate(f.boundary):
        resid[i] += tv[k]
    result = dict(
        q=q, R=R, epsilon=estr, dps=dps, character=[iy, iz], charge=1,
        carrier_complex_dimension=f.n, boundary_dimension=len(f.boundary),
        raw_hessian_check=jet_check, HtJ_residual=hres,
        exterior_pencil_identity_error=pencil_err,
        tB1=tB1, tC1=tC1, tB2=tB2, tC2=tC2,
        tC1_minus_tB1=tC1 - tB1, tB2_minus_tB1=tB2 - tB1, tC2_minus_tB1=tC2 - tB1,
        A_boundary_spectrum_at_tB1=evB[:4],
        A_boundary_spectrum_at_tC1=evA_tC[:4],
        C_boundary_spectrum_at_tC1=evC_tC[:4],
        C_boundary_spectrum_at_tB1=evC_tB[:4],
        A_min_abs_at_tC1=min(abs(x) for x in evA_tC),
        A_negative_count_at_tC1=sum(1 for x in evA_tC if x < 0),
        A_boundary_min_at_0=evA_0[0], C_boundary_min_at_0=evC_0[0],
        interval=ivl,
        unit_kernel_pairing=pairing,
        first_order_shift=first_order, lift_norm_sq=nrm**2,
        first_order_ratio=first_order / (-(nrm**2) * pairing),
        corrected_kernel_augmented_residual=max(abs(x) for x in resid),
        seconds=time.time() - t_start,
        peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    fn = OUTDIR / f'sep_q{q}_R{R}_e{estr}_p{dps}_s{iy}_{iz}{tag}.json'
    fn.write_text(json.dumps(jsonable(result), indent=2) + '\n')
    print('RESULT', fn, 'tC1-tB1', mp.nstr(tC1 - tB1, 15), 'A at tC1', mp.nstr(evA_tC[0], 15),
          mp.nstr(evA_tC[1], 15), 'C at tC1', mp.nstr(evC_tC[0], 15), flush=True)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--q', type=int, default=2)
    p.add_argument('--R', type=int, default=18)
    p.add_argument('--eps', default='1e-100')
    p.add_argument('--dps', type=int, default=400)
    p.add_argument('--iy', type=int, default=7)
    p.add_argument('--iz', type=int, default=7)
    a = p.parse_args()
    run(a.q, a.R, a.eps, a.dps, a.iy, a.iz)
