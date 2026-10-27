#!/usr/bin/env python3
"""Smallest R covered by refute-r1's parameterized family: q=1,R=6.
Computes the period-two transverse sector of its (88,8,8) physical lift.
This sector supplies only diagnostic directions: full-carrier positivity is
NOT inferred. Interior is the single Abelian defect dilU, exterior is Uth.
The background is in the exact family at alpha=160*eps and cap=24*alpha.
Q and C2 use Taylor arithmetic; C2 is also checked by independent
normalized finite differences. No float sign is claimed as a proof.
"""
import sys
sys.dont_write_bytecode=True
import resource
resource.setrlimit(resource.RLIMIT_AS,(1900*1024**2,1900*1024**2))
import gc,itertools,json,time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh,solve,qr
from scipy.optimize import brentq
from assembly import Raw,assemble,expv,P,I
from wide_probe import WideSlab,geometry
from jet2 import raw_jet
OUT=Path(__file__).resolve().parent

class SingleSlab(WideSlab):
    def config(self,theta,eps):
        u={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        u[((self.p,0,0),1)]=expv(np.array([eps,0.,0.]))
        return u

# Jacobian is computed row-locally with Taylor arithmetic (no finite differences).
def local_jac(self,h):
    from types import SimpleNamespace
    em={j:i for i,j in enumerate(self.lat.eidx)}
    ans=np.zeros((len(self.lat.b1)*3,len(em)))
    for row,(d,bg) in enumerate(zip(self.data,self.bg)):
        base,legs=d;used=sorted(set(base).union(*(set(l+m+r) for l,m,r in legs)))
        ix={b:i for i,b in enumerate(used)};cv=lambda p:[ix[b] for b in p]
        sub=Raw.__new__(Raw);sub.lat=SimpleNamespace(nB=len(used),dim=3*len(used))
        sub.u=self.u[used];sub.data=[(cv(base),[(cv(l),cv(m),cv(r)) for l,m,r in legs])];sub.bg=[bg]
        eye=np.eye(sub.lat.dim)
        J=raw_jet(sub,eye)[1].T
        for i,b in enumerate(used):
            for c in range(3):
                if 3*b+c in em:ans[3*row:3*row+3,em[3*b+c]]=J[:,3*i+c]
    return ans
Raw.jac=local_jac


def run(R,eps):
    t0=time.time();lat=SingleSlab(R)
    raw,W,fixed,hj,checks=assemble(lat,eps)
    U=lat.config(0,eps);din=lat.delta_matrix(U,'in')
    B=W.T@din@W+fixed;B=(B+B.T)/2;del din,fixed;gc.collect()
    omitted=[p for p in lat.plaquettes if p not in set(lat.plaq_in) and any(b not in lat._zb_set for b in lat.edges_of(p))]
    edges=sorted({3*lat.bond_index[b]+j for p in omitted for b in lat.edges_of(p) for j in range(3)})
    boundary=np.flatnonzero(np.max(np.abs(W[edges]),axis=0)>2e-13)
    n=len(lat.eidx);nb=len(boundary)
    def shift(t):
        u=lat.config(t,eps);out=np.zeros((nb,nb))
        for p in omitted:
            x,mu,nu=p;re,im=lat._re_im(u,p);aa=np.zeros((4,12,2,2),complex)
            aa[0,6:9]=-np.array([P.rmap(u[(x,nu)],e) for e in P.E])
            aa[1,9:12]=-np.asarray(P.E);aa[2,0:3]=np.asarray(P.E)
            aa[3,3:6]=np.array([P.rmap(u[(x,mu)],e) for e in P.E])
            c=aa.sum(axis=0);bil=-np.einsum('iab,jbc,ca->ij',c,c,re-I).real
            for r,s in itertools.combinations(range(4),2):
                bil+=(-1j*(np.einsum('iab,jbc,ca->ij',aa[r],aa[s],im)-np.einsum('jab,ibc,ca->ij',aa[s],aa[r],im))).real
            gram=(bil+bil.T)/4-.5*np.einsum('iab,jba->ij',c,c).real
            ids=[3*lat.bond_index[b]+j for b in lat.edges_of(p) for j in range(3)]
            w=W[np.ix_(ids,boundary)];out+=w.T@gram@w
        return (out+out.T)/2
    E=np.zeros((n,nb));E[boundary,np.arange(nb)]=1
    Ge=solve(B,E,assume_a='pos');S=solve(Ge[boundary],np.eye(nb),assume_a='pos')
    low=lambda t:float(eigh(S+shift(t),eigvals_only=True)[0])
    ends=[low(0),low(np.pi)];assert ends[0]>0>ends[1]
    root=brentq(low,0,np.pi,xtol=1e-14)
    ev,V=eigh(S+shift(root));ids=np.flatnonzero(np.abs(ev)<1e-9)
    fields=Ge@(S@V[:,ids]);fields,_=qr(fields,mode='economic')
    residual=B@fields;residual[boundary]+=shift(root)@fields[boundary]
    used=sorted({3*i+c for base,legs in raw.data for path in [base]+[p for leg in legs for p in leg] for i in path for c in range(3)})
    wf=W@fields;wf[np.setdiff1d(np.arange(lat.dim),used)]=0
    def quad(z,method):
        amp=np.linalg.norm(z)
        if amp==0:return 0.
        v=z/amp
        c2=raw_jet(raw,v)[2] if method=='jet2' else raw.c2(v,method)
        return float(2*np.dot(hj,c2)*amp*amp)
    projections=[]
    for method in ['jet2',.01,.003,.001]:
        H=np.zeros((len(ids),len(ids)))
        for i in range(len(ids)):
            for j in range(i+1):
                H[i,j]=H[j,i]=(quad(wf[:,i]+wf[:,j],method)-quad(wf[:,i]-wf[:,j],method))/4
        projections.append(dict(method=method,matrix=H.tolist(),eigenvalues=eigh(H,eigvals_only=True).tolist()))
    # One random direction checks Taylor normalization against finite differences.
    rng=np.random.default_rng(19081);v=rng.normal(size=n);v/=np.linalg.norm(v);wv=W@v
    j2=raw_jet(raw,wv)
    checkjet=[dict(h=h,error=float(np.linalg.norm(j2[2]-raw.c2(wv,h)))) for h in [.01,.003,.001]]
    # Forms just before crossing, retaining the entire near-null cluster.
    near=[]
    for dt in [1e-4,1e-8,1e-12]:
        A=B.copy();A[np.ix_(boundary,boundary)]+=shift(root-dt)
        ee,vv=eigh(A,subset_by_index=[0,max(1,len(ids))-1]);ww=W@vv
        vals=[]
        for i in range(len(ee)):vals.append(quad(ww[:,i],'jet2'))
        near.append(dict(theta=root-dt,lowest=ee.tolist(),D_on_lowest=vals))
    row=dict(R=R,epsilon=eps,alpha=160*abs(eps),cap=3840*abs(eps),geometry=geometry(R),
        physical_lift_sides=[12*R+16,8,8],computed_sector_sides=list(lat.sides),
        checks=checks,carrier_dimension=n,boundary_dimension=nb,carrier_endpoints=ends,
        root=root,kernel_dimension=len(ids),boundary_lowest=ev[:12].tolist(),
        kernel_residual_norm=float(np.linalg.norm(residual)),raw_path_norms=np.linalg.norm(wf,axis=0).tolist(),
        projected_D=projections,near_crossing=near,jet_fd_checks=checkjet,
        random_D=float(2*hj@j2[2]),seconds=time.time()-t0,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        warning='Uncertified period-two sector only; no full-carrier unit, corrected singularity, or cofinal conclusion.')
    print(json.dumps(row),flush=True);return row

if __name__=='__main__':
    R=int(sys.argv[1]) if len(sys.argv)>1 else 6
    eps=float(sys.argv[2]) if len(sys.argv)>2 else .0015625
    result=run(R,eps)
    (OUT/('crossing_R%d_eps%g.json'%(R,eps))).write_text(json.dumps(result,indent=2)+'\n')
