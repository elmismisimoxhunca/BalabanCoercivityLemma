#!/usr/bin/env python3
"""All-sector screen of the vacuum (eps = 0) twist carrier at one scale q.

For every charge (0 neutral, 1 charged) and transverse character (iy,iz):
  - double LDL inertia of the localized augmented system (B PD check; the
    required inertia is (n+h positive, h negative), as in round-6 sectors.py),
  - double boundary Schur S of B and the minimum of S + theta(t) at t = 0 and
    at the requested angles.
By the Loewner monotonicity of (B + theta(t))/sin t on (0, pi/2], a sector with
positive minimum at angle t has no crossing on (0, t].  This identifies the
first crossing sector.  Mp assembly at modest precision, DOUBLE spectra: a
screen, not a certificate.  Imports the round-6 probe READ-ONLY.
"""
import sys
sys.dont_write_bytecode = True
PROBE = '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe'
sys.path.insert(0, PROBE)
from sectors import double_inertia            # noqa: E402  (read-only import)
from probe import *                           # noqa: F401,F403
import resource
resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
from scipy.linalg import eigvalsh
HERE = Path(__file__).resolve().parent
OUTDIR = HERE / 'out'
OUTDIR.mkdir(exist_ok=True)


def screen(q, R, angles, dps=20):
    mp.mp.dps = dps
    start = time.time()
    out = OUTDIR / f'screen_q{q}_R{R}_vacuum.json'
    report = dict(q=q, R=R, epsilon='0', assembly_dps=dps, angles=angles,
                  screening_precision='IEEE double', sectors=[])
    for charge in [0, 1]:
        for iy in range(4 * q):
            for iz in range(4 * q):
                f = Family(q, R, mp.mpf(0), iy, iz, charge).assemble()
                inert = double_inertia(f, f.aug)
                ok = inert['positive'] == f.n + f.H.n and inert['negative'] == f.H.n
                lu = splu(f.aug.scipy())
                rhs = np.zeros((f.aug.n, len(f.boundary)), complex)
                rhs[f.boundary, np.arange(len(f.boundary))] = 1
                X = lu.solve(rhs)
                S = np.linalg.inv(X[f.boundary])
                S = (S + S.conj().T) / 2
                th0 = np.array(f.theta(0).tolist(), complex)
                th1 = np.array(f.theta(mp.pi / 2).tolist(), complex)
                mins = [float(eigvalsh(S + np.cos(t) * th0 + np.sin(t) * th1)[0]) for t in [0.0] + angles]
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
