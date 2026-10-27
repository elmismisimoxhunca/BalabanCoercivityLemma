#!/usr/bin/env python3
"""Boundary placement diagnostic; not a Lean certificate.

Geometry: AHP/round5/guarded/ivt-r2/Attempt.lean:986-995.
Variant: Attempt.lean placementPattern/placementU (defect x=4*q+2).
All numerical operator transcriptions are imported read-only from
AHP/round6/probe/probe.py; its complete frozen Lean-line dictionary is
AHP/round6/probe/SOURCES.md. In particular: Q0 and C2_0 are
lean/src/ZXR2Sector.lean:69,97,109 and lean/src/ZLocJet.lean:118;
H and D are lean/src/R2Algebra.lean:149,222; localized source is
lean/src/ZLocJ.lean:49,71 and lean/src/D1Lit.lean:56.

No curvature mask is used as D. Check the full neutral KKT source solve,
its exact candidate multiplier supported at level zero, and the genuine raw-jet/source pairing
on a deterministic charged input. The test input is not reconstructed as
W*v, so this diagnostic is not labelled an evaluation of D on a carrier
vector. The zero positive-level source kills the pairing for every input,
including W*v. No crossing location is needed for the formal zero theorem.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / 'probe'))
import probe as p
import mpmath as mp
import argparse, json, time, resource

class Placement(p.Family):
    def angle(self, b, t=0):
        x, d = b
        if not (self.in0(x) or self.in0(self.shift(x,d))):
            return t
        return self.eps if x[0] == self.lo+2 and x[1]%2 == 0 and x[2]%2 == 0 and d == 1 else 0

def run(q, R, eps, dps):
    start=time.time();mp.mp.dps=dps
    f=Placement(q,R,mp.mpf(eps),0,0,0).assemble()
    hj,res=f.hj()
    # Independently construct the KKT solution (carrier and auxiliary=0,
    # multiplier=J on identity level-zero rows, multiplier_top=0).
    j0=[f.j[f.em[f.bi[b]]] for b in f.b0]+[0]*len(f.b1)
    qsj=f.Q.star().apply(j0)
    exact_rhs_res=max(abs(x-y) for x,y in zip(qsj,f.j))
    active=[f.bonds[j] for j,z in zip(f.e,f.j) if z]
    outside=[b for b in active if b not in set(f.b0)]
    # Test the raw-jet pairing on a general bond field. It is not asserted
    # to be W*v or a crossing vector. The exact zero is input-independent.
    g=Placement(q,R,mp.mpf(eps),0,0,1)
    w=[mp.mpc(((j*17)%31)-15,((j*7)%19)-9)/100 for j in range(len(g.bonds))]
    val,terms=g.correction(w,hj)
    exact_val,exact_terms=g.correction(w,[mp.mpf(0)]*len(hj))
    result=dict(q=q,R=R,epsilon=eps,dps=dps,defect_x=f.lo+2,
        physical_fine_sides=[f.nx,8*q,8*q],Omega0=[f.lo,f.hi],Omega1=[f.p,f.s],
        source_support_longitudinal=sorted(set(b[0][0] for b in active)),
        source_nonzero_count=len(active),source_outside_level0=outside,
        exact_KKT_candidate_residual=exact_rhs_res,
        maximum_computed_positive_level_HtJ=max(map(abs,hj)),
        KKT_solve_relative_residual=res,
        arbitrary_test_correction_computed=val,
        arbitrary_test_correction_exact_candidate=exact_val,
        interpretation='Exact KKT candidate has zero positive-level multiplier. The arbitrary raw-jet input is not asserted to be W*v. Zero pairing is not a positive sign. No crossing or full-carrier unit certified.',
        peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        seconds=time.time()-start)
    out=ROOT/f'placement_q{q}_R{R}_e{eps}_p{dps}.json'
    out.write_text(json.dumps(p.jsonable(result),indent=2)+'\n')
    print(json.dumps(p.jsonable(result),indent=2),flush=True)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--q',type=int,default=1);a.add_argument('--R',type=int,default=18)
    a.add_argument('--eps',default='1e-3');a.add_argument('--dps',type=int,default=80)
    args=a.parse_args();run(args.q,args.R,args.eps,args.dps)
