#!/usr/bin/env python3
"""Independent held-out left-twist check; no Lean/certification claim.

Read-only use of round6/probe's actual-operator transcription. Unlike the round9
wrapper, uses an analytic trigonometric derivative and explicitly checks the full
augmented null residual. All generated files are beside this script.
"""
import os
import sys
sys.dont_write_bytecode = True
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
from pathlib import Path
ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT / 'AHP/round6/probe'))
from leading_source import Family, leading_h, mp, jsonable
import argparse
import json
import resource
import time
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


class LeftFamily(Family):
    def angle(self, b, t=0):
        x, d = b
        y = self.shift(x, d)
        if not (self.in0(x) or self.in0(y)):
            return t if x[0] % self.nx < self.lo else 0
        return self.eps if x[0] == self.p and x[1] % 2 == 0 and x[2] % 2 == 0 and d == 1 else 0


def run(dps):
    mp.mp.dps = dps
    start = time.time()
    q, R, iy, iz = 2, 22, 7, 7
    f = LeftFamily(q, R, mp.mpf(0), iy, iz, 1).assemble()
    S = f.boundary_inverse()
    T0, T1, T2 = f.theta(0), f.theta(mp.pi / 2), f.theta(mp.pi)
    C, A = (T0 + T2) / 2, (T0 - T2) / 2
    B = T1 - C
    theta = lambda t: C + mp.cos(t) * A + mp.sin(t) * B
    theta_prime = lambda t: -mp.sin(t) * A + mp.cos(t) * B
    error = mp.mnorm(theta(mp.mpf('0.371')) - f.theta(mp.mpf('0.371')), 1)
    low = lambda t: mp.eighe(S + theta(t), eigvals_only=True)[0]
    root = mp.findroot(low, (mp.mpf('0.55'), mp.mpf('0.58')),
                       tol=mp.power(10, -dps + 15), verify=True)
    ev, vectors = mp.eighe(S + theta(root))
    y = vectors[:, 0]
    rhs = S * y
    x = [sum(f.X[j][i] * rhs[j] for j in range(len(f.X))) for i in range(f.aug.n)]
    norm = mp.sqrt(sum(abs(z)**2 for z in x[:f.n]))
    x = [z / norm for z in x]
    w = f.dressed(x[:f.n], x[f.n:f.n + f.H.n])
    h = leading_h(f)
    c1, terms = f.correction(w, h)
    boundary_v = mp.matrix([x[i] for i in f.boundary])
    residual = f.aug.apply(x)
    exterior = theta(root) * boundary_v
    for i, b in enumerate(f.boundary):
        residual[b] += exterior[i]
    null_residual = max(map(abs, residual))
    k = -mp.pi / 8
    T = 4 * (1 - mp.cos(k))
    rho = (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2
    # b1 begins with one longitudinal row at p-2; leading_h uses index 2 for
    # the direction-1 row at p. Sum all nonzero terms in physical order.
    active = [(b, z) for b, z in zip(f.b1, terms) if z]
    lead = next(z for b, z in active if b == ((f.p, 0, 0), 1))
    tail = c1 - lead
    # Test the newly compiled SourceDominance sufficient conditions, not just
    # the sign of the total sum. Its n is the number of blocks minus one.
    nblocks = (f.s - f.p) // 2
    gamma = mp.acosh(3)
    alpha = [mp.mpf(3)/2 * (-1)**j * mp.sinh((nblocks-j)*gamma) /
             mp.sinh((nblocks+1)*gamma) for j in range(nblocks)]
    jets = [terms[3*j+2] / (2*h[3*j+2]) for j in range(nblocks)]
    source_residual = max(abs(6*alpha[j] + (alpha[j-1] if j else 0) +
                             (alpha[j+1] if j+1<nblocks else 0) -
                             (mp.mpf(3)/2 if j == 0 else 0)) for j in range(nblocks))
    jet_ratios = [abs(v/jets[0]) for v in jets]
    out = dict(q=q, R=R, character=[iy, iz], twist='left-only', dps=dps,
               root=root, schur_low=[mp.re(e) for e in ev[:4]],
               exact_pencil_slope=mp.re((boundary_v.H * theta_prime(root) * boundary_v)[0]),
               c1=c1, K=c1/rho**(4*q*R), rho=rho,
               null_residual=null_residual, residual_over_c1=null_residual/abs(c1),
               pencil_identity_error=error,
               leading_defect_term=lead, tail=tail,
               nblocks=nblocks, source_equation_residual=source_residual,
               v0=jets[0], max_jet_ratio=max(jet_ratios),
               max_jet_ratio_away_from_0=max(jet_ratios[1:]),
               source_pairing_relative_error=abs(c1/2-jets[0])/abs(jets[0]),
               source_pairing_error_bound=mp.mpf(15)/19,
               abs_tail_over_leading=abs(tail/lead),
               absolute_tail_over_leading=sum(abs(z) for b,z in active if b != ((f.p,0,0),1))/abs(lead),
               first_terms=[dict(bond=b, value=z) for b,z in active[:8]],
               left_half_mass=sum(abs(x[i])**2 for i,j in enumerate(f.e)
                                  if f.bonds[j][0][0] < (f.lo+f.hi)/2),
               peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               seconds=time.time()-start,
               qualification='floating-point evidence only; no interval enclosure or full-character screen')
    target = Path(__file__).resolve().parent / f'left_q2_R22_p{dps}.json'
    target.write_text(json.dumps(jsonable(out), indent=2) + '\n')
    print('RESULT', target, 'c1', mp.nstr(c1,30), 'K', mp.nstr(out['K'],30),
          'residual/c1', mp.nstr(out['residual_over_c1'],6), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--dps', type=int, required=True)
    run(parser.parse_args().dps)
