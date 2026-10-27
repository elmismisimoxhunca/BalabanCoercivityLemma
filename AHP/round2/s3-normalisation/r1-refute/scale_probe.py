#!/usr/bin/env python3
"""Weight/Schur diagnostic, NOT a realized LinkCfg or an admissible witness.

Frozen sources (paths relative to lean/src):
Q: ZXR2Sector.lean:97-107; C:109-111; raw=half D2B:73-89.
Raw level 0 is zero by ZLocJet.lean:104-120.
Mass weights/assembly: ZXR2Ops3.lean:98-115.
Ginv/G/H and corrected K: R2Algebra.lean:145-154.
Nmat/firstTerm: ZXG3A.lean:35-36,50-51.
eta: ZXR2Wire2.lean:37. J scaling: ZLocJ.lean:71-89.

Physical assembly: pin/Statement.lean (verbatim prefix of Attempt.lean):
spacing:44-45; metric:54-55; Q/Qs:115-121; Mass:125-127;
Ginv/G/N0/H:130-142; Cj:160-164; input/output:166-174;
CBil:178-189; HFor:196-199; KBil/G1inv:203-225;
G1/N:227-233; B/firstTerm:238-248.

This only stress-tests the scale chain. Qraw, raw jets, base quadratic
operator, and J below are independent finite arrays, not those actual
operators. W is taken to be identity (not computed); a finite abstract
positive quadratic operator replaces Dpi+T*tT. There is NO geometry,
background, gauge constraint, or claim of actual operator realization.
It can reject a scaling route but cannot close a pinned negative goal.
No compression is inverted. Every N is inverted on all rows first.
"""
from fractions import Fraction as Fr
import json
import resource
resource.setrlimit(resource.RLIMIT_AS, (4_000_000_000, 4_000_000_000))
import numpy as np

# Exact scalar search: coefficients multiplying the same raw bilinear jet.
checks = []
for ell in (2, 3, 5, 13):
    for k in range(2, 7):
        eta = Fr(1, ell**k)
        for j in range(k + 1):
            s = ell**j * eta
            cj = Fr(1, ell**(2*j))
            plain = s * cj
            dimensionless_after_H = (s*s*cj) / s
            expected = eta / ell**j
            checks.append(plain == dimensionless_after_H == expected)
assert all(checks)

runs = []
for ell in (2, 3, 5):
    for k in (2, 3, 4):
        for seed in range(5):
            rng = np.random.default_rng(seed + 100*k + 1000*ell)
            levels = np.repeat(np.arange(k+1), 2)
            nr = len(levels)
            n = nr + 3
            eta = float(ell)**(-k)
            s = float(ell)**levels * eta
            metric = np.diag(s**3)
            qraw = rng.normal(size=(nr, n))
            q = qraw / (float(ell)**levels[:, None])
            mass = q.T @ np.diag(float(ell)**levels) @ q
            # Stand-in for Dpi+T*tT, explicitly NOT a lattice operator.
            t = rng.normal(size=(n,n))
            base = t.T @ t + 4*np.eye(n)
            gi = base + mass
            g = np.linalg.inv(gi)
            h = g @ q.T @ np.linalg.inv(q @ g @ q.T)
            raw = rng.normal(size=(nr,n,n))
            raw = (raw + raw.transpose(0,2,1))*0.5
            raw[levels == 0] = 0
            # Stand-in source; keeps nonzero lower and top cross terms.
            jsrc = 0.0001*rng.normal(size=n)
            cbody = raw / float(ell)**levels[:,None,None]
            ki = gi - 2*np.einsum('r,rij->ij', h.T@jsrc, cbody)
            ni = np.linalg.inv(q @ np.linalg.inv(ki) @ q.T)
            # Weighted physical adjoint, independent assembly of physical mass/H.
            qs = eta**(-3) * q.T @ metric
            massp = qs @ np.diag(s**(-2)) @ q
            gip = eta**(-2)*base + massp
            gp = np.linalg.inv(gip)
            hp = gp @ qs @ np.linalg.inv(q @ gp @ qs)
            # Stored physical Cj has TWO inverse ell^j factors.
            cj = raw / float(ell)**(2*levels[:,None,None])
            readings = {
                'plainH': (hp, s[:,None,None]*cj),
                'dimensionlessH': (hp@np.diag(1/s), s[:,None,None]**2*cj),
                # Deliberately wrong old recipe, diagnostic sensitivity only.
                'wrong_old_plainH_control': (hp, eta**2*raw),
            }
            record = {'ell':ell, 'k':k, 'seed':seed,
                      'min_body_eigenvalue':float(np.linalg.eigvalsh(ki)[0]),
                      'H_relative_error':float(np.linalg.norm(hp-h)/np.linalg.norm(h)),
                      'readings':{}}
            tests = np.eye(nr)[-2:].tolist() + [np.r_[np.zeros(nr-2), [1., 2.]].tolist()]
            for reading, (hr, cr) in readings.items():
                # KBil includes eta^3, then G1inv divides by eta^3.
                kip = gip - 2*np.einsum('r,rij->ij', hr.T@(eta**(-3)*jsrc), cr)
                nip = np.linalg.inv(q @ np.linalg.inv(kip) @ qs)
                ratios = []
                for f in map(np.array, tests):
                    frozen = eta * (f @ ni @ f)
                    printed = f @ metric @ nip @ f
                    ratios.append(float(frozen/printed))
                record['readings'][reading] = {
                    'ratios':ratios, 'spread':max(ratios)-min(ratios),
                    'K_scaling_relative_error':float(np.linalg.norm(kip-eta**(-2)*ki)/np.linalg.norm(eta**(-2)*ki))}
            for reading in ('plainH','dimensionlessH'):
                assert max(abs(x-1) for x in record['readings'][reading]['ratios']) < 1e-9
            runs.append(record)
summary = {'status':'no candidate; abstract scale diagnostic only',
           'exact_coefficient_checks':len(checks), 'matrix_cases':len(runs),
           'max_correct_ratio_error':max(abs(x-1) for r in runs for key in ('plainH','dimensionlessH') for x in r['readings'][key]['ratios']),
           'max_wrong_control_spread':max(r['readings']['wrong_old_plainH_control']['spread'] for r in runs),
           'rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           'runs':runs}
print(json.dumps(summary, indent=2))
