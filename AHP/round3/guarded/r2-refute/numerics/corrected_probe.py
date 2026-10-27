#!/usr/bin/env python3
"""Complete quotient correction by summing genuine raw-row Hessians.

Evidence only; all operator anchors are in wide_probe.py and assembly.py:
 R2Raw1.lean:36,43,68,74; R2RawX.lean:187; ZLocJet.lean:35,39,89,100;
 ZXR2Sector.lean:97,109; R2Algebra.lean:145,149,212,220,222;
 D1Lit.lean:59; pin/Statement.lean:273,290,293.

Each weighted raw output row is evaluated on precisely its finite path edges.
Its scalar Hessian is scattered into the full fine-bond space, then sandwiched
by the SAME computed W. No arbitrary local matrix is substituted for Delta2.
No small coefficient is pruned. Finite differences remain non-certified.
Local B and C inverses are computed on the full QUOTIENT carrier, and only
then their boundary Green blocks are inverted (a Schur complement identity).
This is not the full physical-torus guard or an invariant-sector theorem.
Memory cap is 1900 MiB via assembly; run single-threaded through heavy run.
"""
import sys
sys.dont_write_bytecode = True
import gc,itertools,json,time,resource
from types import SimpleNamespace
import numpy as np
from scipy.linalg import eigh,solve
from scipy.optimize import brentq
from assembly import Raw,assemble,P,I
from wide_probe import WideSlab,geometry,OUT


def raw_hessian(raw,hj,h):
    H=np.zeros((raw.lat.dim,raw.lat.dim))
    for row,(d,bg) in enumerate(zip(raw.data,raw.bg)):
        base,legs=d
        used=sorted(set(base).union(*(set(l+m+r) for l,m,r in legs)))
        remap={b:i for i,b in enumerate(used)}
        cv=lambda path:[remap[b] for b in path]
        sub=Raw.__new__(Raw);sub.lat=SimpleNamespace(nB=len(used),dim=3*len(used))
        sub.u=raw.u[used];sub.data=[(cv(base),[(cv(l),cv(m),cv(r)) for l,m,r in legs])];sub.bg=[bg]
        weight=hj[3*row:3*row+3]
        n=sub.lat.dim;eye=np.eye(n);HH=np.zeros((n,n))
        # No cutoff: even tiny source coefficients are retained.
        def f(A):return sub.eval(A)@weight
        for i in range(n):
            for j in range(0,i+1,32):
                z=eye[j:min(i+1,j+32)];v=eye[i]
                vals=(f(h*(v+z))-f(h*(v-z))-f(h*(-v+z))+f(h*(-v-z)))/(4*h*h)
                HH[i,j:j+len(z)]=vals;HH[j:j+len(z),i]=vals
        ids=[3*b+c for b in used for c in range(3)]
        H[np.ix_(ids,ids)]+=HH
    return (H+H.T)/2


def run(R=2,eps=.08):
    t0=time.time();lat=WideSlab(R);raw,W,fixed,hj,checks=assemble(lat,eps)
    U=lat.config(0,eps);B=W.T@lat.delta_matrix(U,'in')@W+fixed;B=(B+B.T)/2
    del fixed
    print('assemble weighted raw Hessian',R,eps,len(raw.data),flush=True)
    H=raw_hessian(raw,hj,.003);D=W.T@H@W;del H
    H=raw_hessian(raw,hj,.001);Df=W.T@H@W;del H
    checks['hessian_refinement_norm']=float(np.linalg.norm(D-Df,'fro'))
    # Directional check against the original unsplit complete raw evaluator.
    rng=np.random.default_rng(761);v=rng.normal(size=B.shape[0]);v/=np.linalg.norm(v)
    checks['directional_D']=float(v@Df@v)
    checks['directional_raw']=float(2*np.dot(hj,raw.c2(W@v,.001)))
    checks['directional_difference']=abs(checks['directional_D']-checks['directional_raw'])
    Ccoarse=B-D;Ccoarse=(Ccoarse+Ccoarse.T)/2
    D=Df;del Df
    C=B-D;C=(C+C.T)/2
    checks['local_corrected_gap']=float(eigh(C,eigvals_only=True,subset_by_index=[0,0])[0])
    omitted=[p for p in lat.plaquettes if p not in set(lat.plaq_in) and any(b not in lat._zb_set for b in lat.edges_of(p))]
    edge_ids=sorted({3*lat.bond_index[b]+j for p in omitted for b in lat.edges_of(p) for j in range(3)})
    boundary=np.flatnonzero(np.max(np.abs(W[edge_ids]),axis=0)>2e-13)
    n=B.shape[0];ns=len(boundary)
    def shift(t):
        u=lat.config(t,eps);ans=np.zeros((ns,ns))
        for p in omitted:
            x,mu,nu=p;re,im=lat._re_im(u,p)
            aa=np.zeros((4,12,2,2),complex)
            aa[0,6:9]=-np.array([P.rmap(u[(x,nu)],e) for e in P.E])
            aa[1,9:12]=-np.asarray(P.E);aa[2,0:3]=np.asarray(P.E)
            aa[3,3:6]=np.array([P.rmap(u[(x,mu)],e) for e in P.E])
            c=aa.sum(axis=0);bil=-np.einsum('iab,jbc,ca->ij',c,c,re-I).real
            for r,s in itertools.combinations(range(4),2):
                bil+=(-1j*(np.einsum('iab,jbc,ca->ij',aa[r],aa[s],im)-np.einsum('jab,ibc,ca->ij',aa[s],aa[r],im))).real
            gram=(bil+bil.T)/4-.5*np.einsum('iab,jba->ij',c,c).real
            ids=[3*lat.bond_index[b]+j for b in lat.edges_of(p) for j in range(3)]
            w=W[np.ix_(ids,boundary)];ans+=w.T@gram@w
        return (ans+ans.T)/2
    E=np.zeros((n,ns));E[boundary,np.arange(ns)]=1
    Gbe=solve(B,E,assume_a='pos');Gce=solve(C,E,assume_a='pos')
    SB=solve(Gbe[boundary],np.eye(ns),assume_a='pos')
    SC=solve(Gce[boundary],np.eye(ns),assume_a='pos')
    Gcoarse=solve(Ccoarse,E,assume_a='pos')
    SCcoarse=solve(Gcoarse[boundary],np.eye(ns),assume_a='pos')
    low=lambda t,S:float(eigh(S+shift(t),eigvals_only=True)[0])
    ta=brentq(lambda t:low(t,SB),0,np.pi,xtol=1e-13)
    tc=brentq(lambda t:low(t,SC),0,np.pi,xtol=1e-13)
    tcc=brentq(lambda t:low(t,SCcoarse),0,np.pi,xtol=1e-13)
    theta=shift(tc)
    A=B.copy();A[np.ix_(boundary,boundary)]+=theta
    Q=C.copy();Q[np.ix_(boundary,boundary)]+=theta
    aev=eigh(A,eigvals_only=True,subset_by_index=[0,5]);qev,vec=eigh(Q,subset_by_index=[0,0])
    row=dict(R=R,eps=eps,geometry=geometry(R),checks=checks,carrier_dimension=n,boundary_dimension=ns,
      carrier_root=ta,corrected_root=tc,root_difference=tc-ta,
      coarse_step_corrected_root=tcc,corrected_root_refinement_change=tc-tcc,
      full_quotient_carrier_lowest_six_at_corrected=aev.tolist(),
      full_quotient_corrected_lowest_at_corrected=float(qev[0]),
      full_quotient_kernel_residual=float(np.linalg.norm(Q@vec[:,0])),
      correction_norm=float(np.linalg.norm(D,2)),
      seconds=time.time()-t0,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      warning='Finite-difference floating-point quotient separation ONLY; not exact singularity, full-lift guard, class regularity, or cofinal family.')
    print(json.dumps(row),flush=True);return row

if __name__=='__main__':
    payload=dict(status='not a certified counterexample',results=[])
    for eps in (.08,.04):
        payload['results'].append(run(2,eps));gc.collect()
        (OUT/'corrected_results.json').write_text(json.dumps(payload,indent=2))
