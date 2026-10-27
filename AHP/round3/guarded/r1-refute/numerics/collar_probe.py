#!/usr/bin/env python3
"""Exploration only, not a counterexample or proved invariant-sector dictionary.

Round-2 formulas retained in assembly.py (full file/line anchors there) and
in delta_ops.py. New operations:
  A, B: lean/src/R2Algebra.lean:145, lean/src/D1Lit.lean:59;
  D from polarized raw-jet Hessian: lean/src/R2Algebra.lean:212,220,222;
  C=B-D; Theta=A-B; response: round-3 pin/Statement.lean:273,290,293.
  Geometry/base law: lean/src/ZStatementP428.lean:42,51,58,66,73,123,130,140;
  coverage: lean/src/ZR2A.lean:107, lean/src/ZR6A.lean:27,33;
  H: lean/src/R2Algebra.lean:149. Top H is solved with all q0 values zero.

Fine torus quotient (N,2,2) represents a proposed period-two transverse sector
of (N,8,8); this representation is NOT proved. The quotient itself fails TorusOK.
M=ell=2,k=1,a=1. Omega1=[p,p+4), Omega0=[p-2R,p+4+2R).
All endpoints are block aligned, base law/collars and factor-12 site/plaquette
coverage are checked by exhaustive one-dimensional arithmetic on the lifted
slab (transverse directions are full and the covering cubes wrap them).
LambdaOK2 with a positive competitor is NOT supplied; the narrow Omega1 is
insufficient for the required Lambda collar. No ClassCoupled bound is asserted.

The point is to measure genuine-formula return through progressively wider
collars, rather than to relabel the excluded round-2 geometry as admissible.
All dense intermediates are small; RLIMIT_AS=1900MiB, single BLAS thread.
"""
import sys
sys.dont_write_bytecode = True
import json, time, resource
from pathlib import Path
import numpy as np
from scipy.linalg import null_space, orth, solve, eigh
from scipy.sparse import csc_matrix, csr_matrix, coo_matrix, diags
from scipy.sparse.linalg import splu
from scipy.optimize import brentq
from assembly import Slab, Raw, expv, adj3, I, P, E

OUT=Path(__file__).resolve().parent

class Collar(Slab):
    def __init__(self,R):
        self.R=R
        self.p=4*((2*R+7)//4)
        self.lo=self.p-2*R; self.hi=self.p+4+2*R
        N=4*((self.hi+11)//4)
        super().__init__((N,2,2))
    def in_om(self,x):return self.lo<=x[0]<self.hi
    def om1(self,x):return self.p<=x[0]<self.p+4
    def config(self,theta,eps):
        u={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        u[((self.p,0,0),1)]=expv(np.array([eps,0.,0.]))
        u[((self.p+1,1,0),2)]=expv(np.array([0.,0.7*eps,0.]))
        return u


def geometry(lat):
    N=lat.sides[0];R=lat.R;p=lat.p;lo=lat.lo;hi=lat.hi
    om0=set(range(lo,hi));om1=set(range(p,p+4))
    dist=lambda x,y:min(abs(x-y),N-abs(x-y))
    base={x for x in range(N) if any(dist(z,y)<=2*R for z in range(2*(x//2),2*(x//2)+2) for y in om1)}
    block0=all((x//2==y//2) <= ((x in om0)==(y in om0)) for x in range(N) for y in range(N))
    block1=all((x//4==y//4) <= ((x in om1)==(y in om1)) for x in range(N) for y in range(N))
    # Only level-zero cubes are possible: width24; level-one width48 > |Om1|.
    cubes=[{(z+i)%N for i in range(24)} for z in range(0,N,2)]
    cubes=[c for c in cubes if c<=om0 and bool(c-om1)]
    site_cover=all(any(x in c for c in cubes) for x in om0)
    plaq_cover=all(any({x,(x+1)%N}<=c for c in cubes) for x in om0 if (x+1)%N in om0)
    return dict(fine_lift_sides=[N,8,8],Om0=[lo,hi],Om1=[p,p+4],
        torus_arithmetic=(N//2)%2==0 and N//2>2,
        base_law=base==om0,block0=block0,block1=block1,
        collar=all(dist(x,y)>2*R for x in range(N) if x not in om0 for y in om1),
        site_cover=site_cover,plaq_cover=plaq_cover,class_cubes=len(cubes),
        lambda_and_positive_competitor=False)


def assemble_sparse(lat,eps):
    U=lat.config(0.,eps);raw=Raw(lat,U);n=len(lat.eidx)
    qtop=raw.jac(2e-5)
    emap={j:i for i,j in enumerate(lat.eidx)}
    b0cols=np.array([emap[3*lat.bond_index[b]+j] for b in lat.b0 for j in range(3)])
    inside=np.setdiff1d(np.arange(n),b0cols)
    grad=lat.grad(U);lap=grad.T@grad
    qp=[];weights=[]
    for x in sorted(lat.lam0):
        block=np.zeros((3,lap.shape[0]));i=lat.site_index[x];block[:,3*i:3*i+3]=np.eye(3)
        qp.append(block);weights.extend([1.]*3)
    for y in sorted(lat.lam1):
        block=np.zeros((3,lap.shape[0]))
        for o in lat.offs:
            x=tuple((y[j]+o[j])%lat.sides[j] for j in range(3));i=lat.site_index[x]
            trans=raw.hol(raw.u[None],lat.gamma(y,o))[0]
            block[:,3*i:3*i+3]+=adj3(trans)/8
        qp.append(block);weights.extend([2.]*3)
    qp=np.vstack(qp);sid=lat.sidx
    nq=null_space(qp[:,sid],rcond=1e-11)
    ri=orth(lap[np.ix_(sid,sid)]@nq,rcond=1e-11)
    R=np.zeros_like(lap);R[np.ix_(sid,sid)]=ri@ri.T
    gp=np.zeros_like(lap);siteop=lap+qp.T@(np.array(weights)[:,None]*qp)
    gp[np.ix_(sid,sid)]=solve(siteop[np.ix_(sid,sid)],np.eye(len(sid)),assume_a='pos')
    W=np.eye(lat.dim)[:,lat.eidx]-grad@gp@R@grad.T[:,lat.eidx]
    T=R@grad.T[:,lat.eidx]
    # This pruning is an explicit FLOATING diagnostic, never an exact locality proof.
    cutoff=2e-13
    for z in (W,T,qtop): z[np.abs(z)<cutoff]=0.
    Ws=csr_matrix(W);Ts=csr_matrix(T);qs=csr_matrix(qtop)
    weights0=np.zeros(n);weights0[b0cols]=1.
    fixed=Ts.T@Ts+diags(weights0)+2*qs.T@qs
    din=csr_matrix(lat.delta_matrix(U,'in'))
    B=(Ws.T@din@Ws+fixed).tocsc();B=(B+B.T)/2
    # H top: q0=0 constrains all b0 columns to zero; solve in their complement.
    Bii=B[np.ix_(inside,inside)].toarray();qt=qtop[:,inside]
    gq=solve(Bii,qt.T,assume_a='pos');N=qt@gq
    source=lat.jsource(U)
    hj=solve(N,gq.T@source[inside],assume_a='pos')
    # Exact raw paths have finite support; W spreading is measured numerically.
    used=set()
    for base,legs in raw.data:
        used.update(base)
        for left,mid,right in legs:used.update(left+mid+right)
    rows=np.array([3*b+j for b in sorted(used) for j in range(3)])
    active=np.flatnonzero(np.max(np.abs(W[rows]),axis=0)>cutoff)
    def scalar_batch(A):return raw.eval(A)@hj
    def hessian(h):
        wa=W[:,active].T;nc=len(active);D=np.zeros((nc,nc))
        for i in range(nc):
            for st in range(0,nc,32):
                z=wa[st:st+32];v=wa[i]
                D[st:st+len(z),i]=(scalar_batch(h*(v+z))-scalar_batch(h*(v-z))-
                    scalar_batch(h*(-v+z))+scalar_batch(h*(-v-z)))/(4*h*h)
        return (D+D.T)/2
    D=hessian(.003);Dfine=hessian(.001)
    del grad,lap,qp,gp,R,siteop,T,W,din
    return raw,Ws,B,Dfine,active,dict(qtop_rows=len(qtop),V0_dimension=len(inside),
        source_norm=float(np.linalg.norm(source)),HtJ_top_norm=float(np.linalg.norm(hj)),
        correction_dimension=len(active),correction_norm=float(np.linalg.norm(Dfine,2)),
        hessian_refinement_norm=float(np.linalg.norm(D-Dfine,2)),pruning_threshold=cutoff,
        local_top_gap=float(eigh(Bii,eigvals_only=True)[0]),N_gap=float(eigh(N,eigvals_only=True)[0]))


def run(R,eps):
    t0=time.time();lat=Collar(R);print('start',R,lat.sides,geometry(lat),flush=True)
    raw,W,B,D,ids,checks=assemble_sparse(lat,eps)
    n=B.shape[0]
    # Assemble only omitted plaquettes meeting the touching carrier. All other
    # omitted plaquettes have zero W rows in this numerical construction.
    omitted=[p for p in lat.plaquettes if p not in set(lat.plaq_in) and
        any(b not in lat._zb_set for b in lat.edges_of(p))]
    def shift(t):
        U=lat.config(t,eps);ii=[];jj=[];vv=[]
        import itertools
        for p in omitted:
            x,mu,nu=p;bonds=lat.edges_of(p);re,im=lat._re_im(U,p)
            aa=np.zeros((4,12,2,2),complex)
            aa[0,6:9]=-np.array([P.rmap(U[(x,nu)],e) for e in E])
            aa[1,9:12]=-E;aa[2,0:3]=E
            aa[3,3:6]=np.array([P.rmap(U[(x,mu)],e) for e in E])
            c=aa.sum(axis=0)
            rawbil=-np.einsum('iab,jbc,ca->ij',c,c,re-I).real
            for r,s in itertools.combinations(range(4),2):
                rawbil+=(-1j*(np.einsum('iab,jbc,ca->ij',aa[r],aa[s],im)-
                    np.einsum('jab,ibc,ca->ij',aa[s],aa[r],im))).real
            gram=(rawbil+rawbil.T)/4-.5*np.einsum('iab,jba->ij',c,c).real
            ix=[3*lat.bond_index[b]+j for b in bonds for j in range(3)]
            ii.extend(np.repeat(ix,12));jj.extend(np.tile(ix,12));vv.extend(gram.ravel())
        dd=coo_matrix((vv,(ii,jj)),shape=(lat.dim,lat.dim)).tocsr()
        return (W.T@dd@W).tocsc()
    sh=shift(.5)
    if R==2:
        Ucheck=lat.config(.5,eps)
        direct=W.T@csr_matrix(lat.delta_matrix(Ucheck,'all')-lat.delta_matrix(Ucheck,'in'))@W
        checks['omitted_assembly_error']=float(np.max(np.abs((sh-direct).toarray())))
        assert checks['omitted_assembly_error']<1e-11
    boundary=np.unique(sh.nonzero()[0]);ns=len(boundary)
    # Full shift has no support outside this set at the checked exterior angles.
    Eb=np.zeros((n,ns));Eb[boundary,np.arange(ns)]=1
    lu=splu(B);invB_E=lu.solve(Eb);Gbb=invB_E[boundary]
    schurB=solve(Gbb,np.eye(ns),assume_a='pos')
    # Woodbury change in boundary Green matrix; avoids subtracting close inverses.
    Ei=np.zeros((n,len(ids)));Ei[ids,np.arange(len(ids))]=1
    invB_Ei=lu.solve(Ei);Gii=invB_Ei[ids];Gbi=invB_Ei[boundary]
    return_matrix=Gbi@solve(np.eye(len(ids))-D@Gii,D@Gbi.T)
    Gcc=Gbb+return_matrix
    schurC=solve(Gcc,np.eye(ns),assume_a='pos')
    trace=[]
    def value(t,SC):
        th=shift(t)[np.ix_(boundary,boundary)].toarray()
        val=float(eigh(SC+th,eigvals_only=True)[0]);trace.append([float(t),val]);return val
    a0=value(0,schurB);ap=value(np.pi,schurB)
    row=dict(R=R,eps=eps,geometry=geometry(lat),checks=checks,n=n,boundary_dimension=ns,
        boundary_interior_green_norm=float(np.linalg.norm(Gbi,2)),
        correction_to_boundary_green_norm=float(np.linalg.norm(return_matrix,2)),
        local_boundary_green_norm=float(np.linalg.norm(Gbb,2)),
        Schur_change_norm=float(np.linalg.norm(schurC-schurB,2)),carrier_endpoints=[a0,ap])
    if a0>0 and ap<0:
        ta=brentq(lambda t:value(t,schurB),0,np.pi,xtol=2e-13)
        tc=brentq(lambda t:value(t,schurC),0,np.pi,xtol=2e-13)
        row.update(carrier_root=ta,corrected_root=tc,root_shift=tc-ta,
            carrier_schur_gap_at_corrected=value(tc,schurB))
    row.update(seconds=time.time()-t0,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    print(json.dumps(row),flush=True);return row

if __name__=='__main__':
    payload=dict(status='exploratory quotient numerics, no certified guard or in-class separating instance',results=[])
    for R in ([int(v) for v in sys.argv[1:]] or [2,6,18]):
        payload['results'].append(run(R,.08))
        (OUT/'collar_results.json').write_text(json.dumps(payload,indent=2))
