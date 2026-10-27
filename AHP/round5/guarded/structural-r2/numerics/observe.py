#!/usr/bin/env python3
"""Numerical falsification test for a proposed observed inverse bound.

Frozen operators: source anchors in the verbatim assembly.py copy. Observation
is the row-space projection of mask*W, with mask the UNION OF rhoT read balls
in Round3.R2Prove.jetInputZero, NOT the smaller set of actual raw-path edges.

The background is the single-defect wideU family (round3/r3-refute), at R=2,
ell=M=2,k=1,a=1,cap=1,alpha=1/48,epsilon=1/7680. Physical fine torus (40,8,8).
Only the real zero transverse Fourier sector is assembled here, on a period-2
cell. This is a computation on a symmetry sector of the intended lift, not a
claim that the cell itself satisfies TorusOK. No exact Lean dictionary is proved.

No corrected singularity, cofinal failure, or certified error bound is claimed.
BLAS must be single-threaded. assembly.py installs RLIMIT_AS=1900 MiB.
"""
import sys
sys.dont_write_bytecode = True
import itertools, json, time, resource
from pathlib import Path
import numpy as np
from scipy.linalg import eigh, solve, orth, svdvals
from scipy.optimize import brentq
from assembly import assemble, I, P
from wide_probe import WideSlab, geometry

OUT=Path(__file__).resolve().parent
class SingleSlab(WideSlab):
    def config(self,theta,eps):
        u=super().config(theta,eps)
        u[((self.p+1,1,0),2)]=I.copy()
        return u

def run(R=2,cap=1.):
    start=time.time(); alpha=min(cap/24,1.)/2; eps=alpha/160
    lat=SingleSlab(R)
    raw,W,fixed,hj,checks=assemble(lat,eps)
    U=lat.config(0,eps)
    B=W.T@lat.delta_matrix(U,'in')@W+fixed;B=(B+B.T)/2
    del fixed
    omitted=[p for p in lat.plaquettes if p not in set(lat.plaq_in) and
             any(b not in lat._zb_set for b in lat.edges_of(p))]
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
    Eb=np.zeros((n,ns));Eb[boundary,np.arange(ns)]=1
    X=solve(B,Eb,assume_a='pos');Gbb=X[boundary];S=solve(Gbb,np.eye(ns),assume_a='pos')
    # Union of read balls on the PHYSICAL torus, projected to residue classes.
    # All top-level centers have even transverse coordinates. Minimizing over
    # their translates gives precisely the distance on the period-2 cell.
    def dist(x,y):
        return sum(min(abs(x[j]-y[j]),lat.sides[j]-abs(x[j]-y[j])) for j in range(3))
    centers={b[0] for b in lat.b1};rho=8 # rhoT 2 1
    observed_sites={x for x in lat.sites if any(dist(x,b)<=rho for b in centers)}
    obs=np.array([3*i+c for i,b in enumerate(lat.bonds) if b[0] in observed_sites for c in range(3)])
    O=W[obs]
    basis=orth(O.T,rcond=1e-10)
    # J=basis*basis^T; norms of Jx equal norms of basis^T x.
    Y=basis.T@X@S
    root=brentq(lambda t:eigh(S+shift(t),eigvals_only=True)[0],0,np.pi,xtol=2e-14)
    ev,v=eigh(S+shift(root));v=v[:,np.argmin(np.abs(ev))]
    z=X@(S@v);z/=np.linalg.norm(z)
    Az=B@z;Az[boundary]+=shift(root)@z[boundary]
    rows=[]
    for d in [1e-2,1e-3,1e-4,1e-5,1e-6,1e-7]:
        theta=root-d;th=shift(theta);H=S+th
        F=Y@solve(H,th,assume_a='sym')
        norm=float(svdvals(F)[0]); M=B.copy();M[np.ix_(boundary,boundary)]+=th
        eig=eigh(M,eigvals_only=True,subset_by_index=[0,0])[0]
        # Check the same transfer against a direct full carrier solve, not an
        # inverse of a compression. Eb is an isometric input inclusion.
        direct=solve(M,Eb@th,assume_a='sym')
        err=float(np.linalg.norm(basis.T@direct-F,2)/max(norm,1.))
        res=float(np.linalg.norm(M@direct-Eb@th,2))
        rows.append(dict(offset=d,theta=theta,carrier_min=float(eig),observed_transfer_norm=norm,
                         offset_times_norm=d*norm,schur_vs_direct_relative_error=err,
                         direct_solve_residual=res))
        print(json.dumps(rows[-1]),flush=True)
    used=set()
    for base,legs in raw.data:
        used.update(base)
        for l,m,r in legs:used.update(l+m+r)
    used=np.array([3*b+c for b in sorted(used) for c in range(3)])
    wp=W@z
    hol=lat.holonomy(U,((lat.p,0,0),0,1))
    # Compare the sum-of-plaquette transcription with the existing dense code.
    direct_shift=W.T@(lat.delta_matrix(lat.config(.5,eps),'all')-lat.delta_matrix(U,'in'))@W
    tmp=np.zeros_like(direct_shift);tmp[np.ix_(boundary,boundary)]=shift(.5)
    shift_err=float(np.max(np.abs(tmp-direct_shift)))
    # Refinement of the only finite-difference ingredient used in A: Q's first jet.
    q0=raw.jac(2e-5);q1=raw.jac(1e-5)
    dq=2*(q1.T@q1-q0.T@q0)
    qerror=float(np.linalg.norm(q0-q1,2)); Aerror=float(np.linalg.norm(dq,2))
    data=dict(status='floating-point evidence only; no pinned goal closed',R=R,cap=cap,
        alpha=alpha,epsilon=eps,geometry=geometry(R),physical_fine_sides=[12*R+16,8,8],
        computed_cell_sides=list(lat.sides),sector=[0,0],carrier_dimension=n,
        boundary_dimension=ns,checks=checks,carrier_crossing=root,
        crossing_residual=float(np.linalg.norm(Az)),crossing_observed_norm=float(np.linalg.norm(basis.T@z)),
        crossing_raw_path_W_norm=float(np.linalg.norm(wp[used])),
        observation_rank=basis.shape[1],observation_rows=len(obs),rhoT=rho,
        raw_path_rows=len(used),holonomy_minus_identity_norm=float(np.linalg.norm(hol-I)),
        shift_transcription_error=shift_err,jacobian_refinement_error=qerror,
        mass_matrix_refinement_error=Aerror,rows=rows,
        seconds=time.time()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    assert shift_err<1e-10
    assert all(r['carrier_min']>20*Aerror for r in rows)
    assert all(r['schur_vs_direct_relative_error']<1e-6 for r in rows)
    assert rows[-1]['observed_transfer_norm']>10000*rows[0]['observed_transfer_norm']
    (OUT/'observation_results.json').write_text(json.dumps(data,indent=2))
    print('DONE',data['seconds'],data['peak_rss_kib'],flush=True)
    return data

if __name__=='__main__':run()
