#!/usr/bin/env python3
"""Evidence only: four exterior transverse links incident to one exterior site.
The interior flat resolvent is reconstructed from ALL transverse characters.
"""
import sys
sys.dont_write_bytecode = True
from single_plaquette_probe import *
from scipy.sparse.linalg import splu
from scipy.sparse import coo_matrix
from scipy.optimize import brentq


def patch_data(lo):
    plaquettes = []
    for d in [1, 2]:
        for side in [0, -1]:
            x = [lo-1, 0, 0]; x[d] = side; x = tuple(x)
            xn = list(x); xn[d] += 1; xn = tuple(xn)
            xm = (lo, x[1], x[2])
            plaquettes.append((d, side, [(xn, 0), (x, 0), (xm, d)]))
    bonds = list(dict.fromkeys(b for _, _, es in plaquettes for b in es))
    return plaquettes, bonds


def patch_matrix(t, charge, plaquettes, bonds, variant):
    mat = np.zeros((len(bonds), len(bonds)), complex)
    for d, side, es in plaquettes:
        angle = -t if variant == 'site-gauge' and side == -1 else t
        # local_hessian uses a1, a3, a4 in that order.
        ids = [bonds.index(b) for b in es]
        mat[np.ix_(ids, ids)] += local_hessian(angle, charge)
    return mat


def run_star(q, R):
    start = time.time(); mp.mp.dps = 25
    plaquettes, bonds = patch_data(4*q)
    n = len(bonds)
    C = np.zeros((n, n), complex); residual = 0.
    trials = []
    for tangential in [0., 0.25]:
        trial = np.zeros(n, complex)
        for i, (x, d) in enumerate(bonds):
            if d == 0:
                trial[i] = 1 if x[1:] == (0, 0) else (-0.25j if max(x[1:]) > 0 else 0.25j)
            elif d == 1 and x[1:] == (0, 0):
                trial[i] = 1j*tangential
        trials.append(trial)
    trial_flat = np.zeros(2); max_F_trial = 0.
    for iy in range(4*q):
        for iz in range(4*q):
            f = Family(q, R, mp.mpf(0), iy, iz, 1).assemble()
            ext, _ = f.plaq('out', 0)
            rows, cols, vals = [], [], []
            for i, row in enumerate(ext.r):
                if i not in f.em: continue
                for j, v in row.items():
                    if j in f.em:
                        rows.append(f.em[i]); cols.append(f.em[j]); vals.append(complex(v))
            A = f.aug.scipy() + coo_matrix((vals, (rows, cols)), shape=(f.aug.n, f.aug.n)).tocsc()
            idx_phase = [f.index(*b) for b in bonds]
            ids = [f.em[i] for i, _ in idx_phase]
            phases = np.array([complex(p) for _, p in idx_phase])
            rhs = np.zeros((A.shape[0], n), complex)
            rhs[ids, range(n)] = phases.conj()
            for ti, trial in enumerate(trials):
                tv = np.zeros(f.n, complex)
                for i, idx in enumerate(ids): tv[idx] += phases[i].conjugate()*trial[i]
                trial_flat[ti] += np.vdot(tv, A[:f.n, :f.n]@tv).real/(4*q)**2
                max_F_trial = max(max_F_trial, float(np.max(np.abs(f.F.scipy()@tv))))
            sol = splu(A).solve(rhs)
            residual = max(residual, float(np.max(np.abs(A@sol-rhs))))
            C += phases[:, None] * sol[ids, :] / (4*q)**2
    C = (C+C.conj().T)/2; S = np.linalg.inv(C)
    reports = []
    for variant in ['uniform', 'site-gauge']:
        for charge in [0, 1]:
            def mat(t): return S+patch_matrix(t, charge, plaquettes, bonds, variant)-patch_matrix(0, charge, plaquettes, bonds, variant)
            def small(t): return np.linalg.eigvalsh(mat(t))[0]
            grid = np.linspace(0, np.pi, 1001)
            roots = [brentq(small, a, b) for a,b in zip(grid[:-1], grid[1:]) if small(a)*small(b)<0]
            reports.append(dict(variant=variant, charge=charge, roots=roots, half_pi_min=float(small(np.pi/2)), pi_min=float(small(np.pi)), crossing_spectra=[np.linalg.eigvalsh(mat(t)).tolist() for t in roots]))
    delta = patch_matrix(np.pi/2, 1, plaquettes, bonds, 'uniform') - patch_matrix(0, 1, plaquettes, bonds, 'uniform')
    trial_values = [float(trial_flat[i] + np.vdot(v, delta@v).real) for i,v in enumerate(trials)]
    result=dict(q=q,R=R,bonds=bonds, sectors=(4*q)**2, reports=reports, residual=residual, trial_energy_at_half_pi=trial_values, trial_gauge_rhs_max=max_F_trial, seconds=time.time()-start, peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, method='all-character flat augmented resolvent; nine physical boundary bonds', caveat='double-precision evidence only; no Lean/operator equivalence or cofinal proof')
    (Path(__file__).parent/f'star_q{q}_R{R}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--q',type=int,default=1); ap.add_argument('--R',type=int,default=18)
    a=ap.parse_args(); run_star(a.q,a.R)
