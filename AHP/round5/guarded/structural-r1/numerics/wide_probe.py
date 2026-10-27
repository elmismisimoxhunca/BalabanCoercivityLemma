#!/usr/bin/env python3
"""Evidence only: widen the top domain to repair the previous Lambda obstruction.

Uses actual-formula transcriptions in assembly.py/delta_ops.py (their headers
cite every frozen operator). No invariant-sector or exact singularity theorem.
Additional anchors, relative to lean/src:
 ZStatementP428.lean:42,51,58,66,73,123,130,140,189,230,286: geometry,
 class cubes, Lambda collar, staircase/dropped tests and torus compatibility;
 ZT4A.lean:57,88: Lambda block sum and LambdaOK2;
 ZR2A.lean:107,121 and ZR6A.lean:27,33: coverage and touching support;
 R2Algebra.lean:145,149,212,220,222: B, H, polarized correction D;
 D1Lit.lean:59: selector assembly. Theta=A-B is the actual-formula difference.
 AHP/round3/guarded/pin/Statement.lean:273,290,293 motivates the boundary
 reduction. Our Schur complement is not identified with that exact range space.

ell=M=2,k=1,a=1; even R; fine lift sides (12R+16,8,8).
Omega1=[2R+4,10R+12); Omega0=[4,12R+12).
Lambda unit strip=[3R+4,3R+6), transverse directions full.
Computation uses the period-two transverse quotient (N,2,2); quotient TorusOK
fails and the full lifted guard is NOT inferred. Class regularity unproved.
Finite differences are restricted to actual raw-path edges and normalized
before differentiation, to avoid subtracting near-zero tiny collar signals.
RLIMIT_AS=1900 MiB is installed by assembly.py; single-threaded BLAS required.
"""
import sys
sys.dont_write_bytecode = True
import gc, itertools, json, time, resource
from pathlib import Path
import numpy as np
from scipy.linalg import eigh, solve, qr
from scipy.optimize import brentq
from assembly import Slab, assemble, expv, I, P

OUT=Path(__file__).resolve().parent

class WideSlab(Slab):
    def __init__(self,R):
        assert R>=2 and R%2==0
        self.R=R; self.p=2*R+4; self.q=10*R+12
        self.lo=4; self.hi=12*R+12
        super().__init__((12*R+16,2,2))
    def in_om(self,x):return self.lo<=x[0]<self.hi
    def om1(self,x):return self.p<=x[0]<self.q
    def config(self,theta,eps):
        u={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        u[((self.p,0,0),1)]=expv(np.array([eps,0.,0.]))
        u[((self.p+1,1,0),2)]=expv(np.array([0.,0.7*eps,0.]))
        return u


def geometry(R):
    N=12*R+16;p=2*R+4;q=10*R+12;lo=4;hi=12*R+12
    o0=set(range(lo,hi));o1=set(range(p,q));L=set(range(3*R+4,3*R+6))
    def pd(n,x,y):return min(abs(x-y),n-abs(x-y))
    base={x for x in range(N) if any(pd(N,z,y)<=2*R for z in range(2*(x//2),2*(x//2)+2) for y in o1)}
    # DescribedAt may occur at j=0 or 1; uniqueness checked by the interval sets.
    desc=[]
    for j in (0,1):
        side=2*2**j
        for z in range(0,N,side):
            c=frozenset((z+i)%N for i in range(12*side))
            if (j==0 and c<=o0 and bool(c-o1)) or (j==1 and c<=o1):desc.append((j,c))
    cubes=[c for j,c in desc if all(j==j2 for j2,c2 in desc if c2==c)]
    top_unit={x for x in range(N//2) if 2*x in o1}
    return dict(fine_lift_sides=[N,8,8],Om0=[lo,hi],Om1=[p,q],Lambda=[3*R+4,3*R+6],
      torus_arithmetic=N%4==0 and N//2>2,
      base_law=base==o0,
      block0=all(((x//2==y//2) <= ((x in o0)==(y in o0))) for x in range(N) for y in range(N)),
      block1=all(((x//4==y//4) <= ((x in o1)==(y in o1))) for x in range(N) for y in range(N)),
      collar=all(pd(N,x,y)>2*R for x in range(N) if x not in o0 for y in o1),
      site_cover=all(any(x in c for c in cubes) for x in o0),
      plaq_cover=all(any({x,(x+1)%N}<=c for c in cubes) for x in o0 if (x+1)%N in o0),
      lambda_block_arithmetic=(3*R+4)%2==0,
      lambda_subset=L<=top_unit,
      lambda_collar=all(pd(N//2,x,y)>2*R for x in L for y in range(N//2) if y not in top_unit),
      class_cubes=len(cubes),positive_competitor_not_certified=True)


def run(R,eps):
    t0=time.time();lat=WideSlab(R);geo=geometry(R)
    print('start',R,eps,geo,flush=True)
    raw,W,fixed,hj,checks=assemble(lat,eps)
    U=lat.config(0,eps)
    B=W.T@lat.delta_matrix(U,'in')@W+fixed;B=(B+B.T)/2
    del fixed
    # Evaluate omitted plaquettes meeting the carrier in their 12D edge spaces.
    omitted=[p for p in lat.plaquettes if p not in set(lat.plaq_in) and
        any(b not in lat._zb_set for b in lat.edges_of(p))]
    edge_ids=sorted({3*lat.bond_index[b]+j for p in omitted for b in lat.edges_of(p) for j in range(3)})
    boundary=np.flatnonzero(np.max(np.abs(W[edge_ids]),axis=0)>2e-13)
    ns=len(boundary); n=B.shape[0]
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
    Ge=solve(B,Eb,assume_a='pos');Gbb=Ge[boundary];S=solve(Gbb,np.eye(ns),assume_a='pos')
    if R==2:
        direct=W.T@(lat.delta_matrix(lat.config(.5,eps),'all')-lat.delta_matrix(U,'in'))@W
        test=np.zeros_like(direct);test[np.ix_(boundary,boundary)]=shift(.5)
        checks['shift_transcription_error']=float(np.max(np.abs(direct-test)))
        assert checks['shift_transcription_error']<1e-10
        del direct,test
    def low(t):return float(eigh(S+shift(t),eigvals_only=True)[0])
    ends=[low(0),low(np.pi)]
    row=dict(R=R,eps=eps,geometry=geo,checks=checks,carrier_dimension=n,boundary_dimension=ns,carrier_endpoints=ends)
    if ends[0]>0 and ends[1]<0:
        root=brentq(low,0,np.pi,xtol=1e-13)
        ev,v=eigh(S+shift(root)); ids=np.flatnonzero(np.abs(ev)<1e-8)
        fields=Ge@(S@v[:,ids]);fields,_=qr(fields,mode='economic')
        used=set()
        for base,legs in raw.data:
            used.update(base)
            for left,mid,right in legs:used.update(left+mid+right)
        used=np.array([3*b+j for b in sorted(used) for j in range(3)])
        wf=W@fields; wf[np.setdiff1d(np.arange(lat.dim),used)]=0
        def quad(z,h):
            amp=np.linalg.norm(z)
            if amp==0:return 0.
            a=z/amp
            return float(2*np.dot(hj,raw.c2(a,h))*amp*amp)
        projections=[]
        for h in (.01,.003,.001):
            D=np.zeros((len(ids),len(ids)))
            for i in range(len(ids)):
                for j in range(i+1):
                    D[i,j]=D[j,i]=(quad(wf[:,i]+wf[:,j],h)-quad(wf[:,i]-wf[:,j],h))/4
            projections.append(dict(h=h,matrix=D.tolist(),eigenvalues=eigh(D,eigvals_only=True).tolist()))
        Av=B@fields;Av[boundary]+=shift(root)@fields[boundary]
        row.update(carrier_root=root,near_zero_boundary_modes=len(ids),boundary_lowest=ev[:10].tolist(),
          kernel_residual_norm=float(np.linalg.norm(Av,2)),raw_path_field_norms=np.linalg.norm(wf,axis=0).tolist(),
          projected_D=projections,
          warning='Projected D is a finite-difference diagnostic at a numerical carrier root, NOT corrected singularity or a guarded witness.')
    row.update(seconds=time.time()-t0,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    print(json.dumps(row),flush=True);return row

if __name__=='__main__':
    payload=dict(status='exploratory only; no exact in-class witness',geometry_only=[geometry(R) for R in (2,4,6,18)],results=[])
    for R in ([int(x) for x in sys.argv[1:]] or [2,4,6]):
        payload['results'].append(run(R,.08));gc.collect()
        (OUT/'wide_results.json').write_text(json.dumps(payload,indent=2))
