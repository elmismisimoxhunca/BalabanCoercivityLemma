#!/usr/bin/env python3
"""Evidence only: single physical exterior-link twist, via full flat Fourier resolvent.
Only the frozen R6 numerical transcription is reused. No interval certificate.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'AHP/round6/probe'))
from probe import Family, mp, np
import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu
from scipy.optimize import brentq, minimize_scalar
import argparse, json, time


def local_hessian(t, charge):
    # Ordered nonzero contributions a1, a3, a4; a2 is the exterior (zero) field.
    cs = np.array([-np.exp(2j * charge * t), 1, 1])
    out = np.cos(t) * np.outer(cs.conj(), cs)
    if charge:
        for r in range(3):
            for s in range(r + 1, 3):
                v = 1j * np.sin(t) * cs[r].conjugate() * cs[s]
                out[r, s] += v
                out[s, r] += v.conjugate()
    return out


def run(q, R):
    start = time.time()
    mp.mp.dps = 25
    C = np.zeros((3, 3), dtype=complex)
    residual = 0.0
    for iy in range(4 * q):
        for iz in range(4 * q):
            f = Family(q, R, mp.mpf(0), iy, iz, 1).assemble()
            # All-plaquette flat carrier: exact augmented localized operator + exterior curl.
            ext, _ = f.plaq('out', 0)
            rows, cols, vals = [], [], []
            for i, row in enumerate(ext.r):
                if i not in f.em:
                    continue
                for j, v in row.items():
                    if j in f.em:
                        rows.append(f.em[i]); cols.append(f.em[j]); vals.append(complex(v))
            A = f.aug.scipy() + coo_matrix((vals, (rows, cols)), shape=(f.aug.n, f.aug.n)).tocsc()
            bonds = [((f.lo - 1, 1, 0), 0), ((f.lo - 1, 0, 0), 0), ((f.lo, 0, 0), 1)]
            ids = [f.em[f.bi[b]] for b in bonds]
            rhs = np.zeros((A.shape[0], 3), complex)
            rhs[ids, range(3)] = 1
            sol = splu(A).solve(rhs)
            residual = max(residual, float(np.max(np.abs(A @ sol - rhs))))
            C += sol[ids, :] / (4*q)**2
            print('sector', iy, iz, 'done', flush=True)
    C = (C + C.conj().T)/2
    S = np.linalg.inv(C)
    reports = []
    for charge in [0, 1]:
        def small(t):
            return np.linalg.eigvalsh(S + local_hessian(t, charge) - local_hessian(0, charge))[0]
        grid = np.linspace(0, np.pi, 1001)
        roots = [brentq(small, a, b) for a, b in zip(grid[:-1], grid[1:]) if small(a)*small(b) < 0]
        opt = minimize_scalar(small, bounds=(0, np.pi), method='bounded')
        reports.append(dict(charge=charge, roots=roots, half_pi_min=float(small(np.pi/2)), pi_min=float(small(np.pi)), grid_min=float(min(map(small, grid))), optimizer_min=float(opt.fun), optimizer_angle=float(opt.x), crossing_spectra=[np.linalg.eigvalsh(S+local_hessian(t, charge)-local_hessian(0, charge)).tolist() for t in roots]))
    result = dict(q=q, R=R, method='double-precision full flat augmented Fourier resolvent; single physical exterior link', caveat='floating-point evidence only; no cofinal, kernel, or noncancellation proof', resolvent_real=C.real.tolist(), resolvent_imag=C.imag.tolist(), schur_eigenvalues=np.linalg.eigvalsh(S).tolist(), residual=residual, sectors=(4*q)**2, reports=reports, seconds=time.time()-start, peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    target = Path(__file__).parent / f'single_q{q}_R{R}.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--q', type=int, default=1); ap.add_argument('--R', type=int, default=2)
    a = ap.parse_args(); run(a.q, a.R)
