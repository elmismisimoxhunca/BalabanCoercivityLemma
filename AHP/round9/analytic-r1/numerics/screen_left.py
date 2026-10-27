#!/usr/bin/env python3
"""All-sector screen of the LEFT-twist vacuum carrier (eps = 0) at one scale q.

Copy of AHP/round8/guarded-idea/numerics/screen.py with the round-6 Family replaced by
lefttwist.LeftFamily (twist only on exterior bonds with base coordinate < lo).  For
every charge (0 neutral, 1 charged) and character (iy, iz): double LDL inertia of the
localized augmented system (B PD check, identical to the round-8 screen since B does not
see the exterior), the double boundary Schur S of B, and the minimum of
S + Theta_left(t) at t = 0 and at the requested angles, with the affine pencil
Theta_left(t) = C + cos t A + sin t B recovered from t = 0, pi/2, pi.
Mp assembly at modest precision, DOUBLE spectra: a screen, not a certificate.
"""
import sys
sys.dont_write_bytecode = True
PROBE = '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe'
sys.path.insert(0, PROBE)
from sectors import double_inertia            # noqa: E402  (read-only import)
from lefttwist import *                       # noqa: F401,F403
from scipy.linalg import eigvalsh


def screen(q, R, angles, dps=20):
    mp.mp.dps = dps
    start = time.time()
    out = OUTDIR / f'screen_left_q{q}_R{R}_vacuum.json'
    report = dict(q=q, R=R, epsilon='0', family='left-only exterior twist', assembly_dps=dps,
                  angles=angles, screening_precision='IEEE double', sectors=[])
    for charge in [0, 1]:
        for iy in range(4 * q):
            for iz in range(4 * q):
                f = LeftFamily(q, R, mp.mpf(0), iy, iz, charge).assemble()
                inert = double_inertia(f, f.aug)
                ok = inert['positive'] == f.n + f.H.n and inert['negative'] == f.H.n
                lu = splu(f.aug.scipy())
                rhs = np.zeros((f.aug.n, len(f.boundary)), complex)
                rhs[f.boundary, np.arange(len(f.boundary))] = 1
                X = lu.solve(rhs)
                S = np.linalg.inv(X[f.boundary])
                S = (S + S.conj().T) / 2
                t0m = np.array(f.theta(0).tolist(), complex)
                t1m = np.array(f.theta(mp.pi / 2).tolist(), complex)
                t2m = np.array(f.theta(mp.pi).tolist(), complex)
                Cm, Am = (t0m + t2m) / 2, (t0m - t2m) / 2
                Bm = t1m - Cm
                mins = [float(eigvalsh(S + Cm + np.cos(t) * Am + np.sin(t) * Bm)[0])
                        for t in [0.0] + angles]
                report['sectors'].append(dict(charge=charge, character=[iy, iz], B_inertia_ok=ok,
                                              B_inertia=inert, schur_min_at_0=mins[0],
                                              schur_min_at_angles=mins[1:]))
                report['seconds'] = time.time() - start
                report['peak_rss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
                out.write_text(json.dumps(report, indent=1) + '\n')
                print('SECTOR', charge, iy, iz, ok, mins, flush=True)
    report['complete'] = True
    out.write_text(json.dumps(report, indent=1) + '\n')


if __name__ == '__main__':
    q = int(sys.argv[1]); R = int(sys.argv[2])
    angles = [float(a) for a in sys.argv[3:]]
    screen(q, R, angles)
