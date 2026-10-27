#!/usr/bin/env python3
"""Exploration only: genuine formulas on a SMALL, OUT-OF-REGIME slab.

No substitution of a finite difference of Delta for Delta2 is made. This probes
Delta2 quadratic forms via the actual raw second jet and H, not its full matrix.
No class, tower admissibility, cofinal family or exact unit is certified.

Lean formula anchors (all relative to lean/src/):
  geomOf: ZXR2Wire1.lean:20; bondsOm0/bondSupp/bondsLam: ZXR2Ops3.lean:26,30,50.
  Delta/curl/holonomy: delta_ops.py header (copied verbatim from Stage A).
  grad: AdalyFormal/Balaban/CovariantOperators.lean:301; lap: R2Ops1.lean:108.
  site Q': R2Ops1.lean:135,141; stepAverage: AdalyFormal/Balaban/QjComposite.lean:675.
  NQp, RImage, Rproj: R2Ops1.lean:150,166,170.
  Qpa, Gp, Wop, Tfull: ZR2Ops2.lean:27,63,67,100.
  J: ZLocJ.lean:20,49,71; minus sign JfS: D1Lit.lean:56.
  DstarDir: AdalyFormal/Balaban/SourceJ.lean:228.
  rProdAux/rProd/sBlock/rawStep: R2Raw1.lean:36,43,68,74 (s=1, ell=2).
  blocked map: AdalyFormal/Balaban/UbarTowerCovariance.lean:237.
  staircase order 2,1,0: AdalyFormal/Balaban/TowerLawCovariant.lean:171.
  exp/log: AdalyFormal/Balaban/SuTwoLogExpCore.lean:164,226 (log away from -1).
  qStep: R2RawX.lean:187; local jets: ZLocJet.lean:35,39,89,100.
  Qfull, C2full: ZXR2Sector.lean:97,109 (level 0 identity/zero; level 1 /ell).
  baseData: ZXR2Ops3.lean:134; massW/MassFull: same file:98,102.
  Ginv, H, Delta2_spec: R2Algebra.lean:145,149,222.

Geometry: fine side (8,4,4), ell=2,k=1; Om0=0<=x<6,
Om1=2<=x<4, Om_j empty for j>=2. Lam_j from geomOf.
This fails TorusOK (unit transverse sides=2), and is not a headline example.
At fixed epsilon, theta changes only Zb bonds. Non-flat interior defects are
in Om1. All top raw paths and site constraints are evaluated explicitly.
Finite differences use h=2e-5 for Q, and a refinement sweep for C2.
Round-2 extension: Slab(sides=(8,8,8)) repeats the two noncommuting
interior defects every four transverse sites. Unit sides then equal (4,4,4),
satisfying TorusOK at ell=M=2, but NOT certifying admissibility/coverage.
Round-3 copy: process address space is capped to 1900 MiB (below 2 GB).
Use collar_probe.py for the round-3 experiment. The original main below and
historical geometry description are retained for provenance and were not run.
"""
import sys
sys.dont_write_bytecode = True
import resource
resource.setrlimit(resource.RLIMIT_AS, (1900*1024**2, 1900*1024**2))  # round-3: below 2 GB
import itertools
import json
import time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh, null_space, orth, solve
from scipy.optimize import brentq
import delta_ops as P

OUT = Path(__file__).resolve().parent
E = np.asarray(P.E)
I = P.I2

def dagger(a):
    return a.swapaxes(-1, -2).conj()

def coords(a):
    return np.stack([a[...,0,0].imag, a[...,0,1].real, a[...,0,1].imag], axis=-1)

def expv(v):
    r = np.linalg.norm(v, axis=-1)
    return np.cos(r)[...,None,None]*I + np.sinc(r/np.pi)[...,None,None]*np.einsum('...a,aij->...ij',v,E)

def logv(g):
    v = coords((g-dagger(g))/2)
    r = np.linalg.norm(v,axis=-1)
    t = np.trace(g,axis1=-2,axis2=-1).real/2
    ang = np.arctan2(r,t)
    ratio = np.ones_like(r)
    np.divide(ang,r,out=ratio,where=r>1e-15)
    if np.any((r<1e-12)&(t<0)):
        raise ValueError('principal log near -1: reject candidate')
    return v*ratio[...,None]

def adj3(u):
    return np.stack([coords(u @ e @ dagger(u)) for e in E],axis=-1)

class Slab(P.Lattice):
    def __init__(self, sides=(8,4,4)):
        self.sides=sides
        self.sites=list(itertools.product(*[range(n) for n in self.sides]))
        self.site_index={s:i for i,s in enumerate(self.sites)}
        self.bonds=[(s,mu) for s in self.sites for mu in range(3)]
        self.bond_index={b:i for i,b in enumerate(self.bonds)}
        self.plaquettes=[(s,mu,nu) for s in self.sites for mu,nu in [(0,1),(0,2),(1,2)]]
        self.nB=len(self.bonds); self.nP=len(self.plaquettes); self.dim=3*self.nB
        self.both=[]; self.zb=[]; self.shell=[]
        for b in self.bonds:
            a=self.in_om(b[0]); z=self.in_om(self.shift(*b))
            (self.both if a and z else self.zb if not a and not z else self.shell).append(b)
        self.plaq_in=[p for p in self.plaquettes if self.corners_in(p)]
        self._zb_set=set(self.zb)
        self.eidx=np.array([3*i+j for i,b in enumerate(self.bonds) if b not in self._zb_set for j in range(3)])
        self.sidx=np.array([3*i+j for i,s in enumerate(self.sites) if self.in_om(s) for j in range(3)])
        self.lam0={s for s in self.sites if self.in_om(s) and not self.om1(s)}
        self.lam1={s for s in self.sites if self.om1(s) and all(x%2==0 for x in s)}
        self.b0=[b for b in self.bonds if (b[0] in self.lam0 or self.shift(*b) in self.lam0)
                 and not (self.om1(b[0]) or self.om1(self.shift(*b)))]
        self.b1=[b for b in self.bonds if b[0] in self.lam1 or self.shift(b[0],b[1],2) in self.lam1]
        self.offs=list(itertools.product(range(2),repeat=3))
    def shift(self,x,mu,n=1):
        y=list(x);y[mu]=(y[mu]+n)%self.sides[mu];return tuple(y)
    def in_om(self,x): return x[0]<6
    def om1(self,x): return 2<=x[0]<4
    def config(self,theta,eps):
        u={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        for y in range(0,self.sides[1],4):
            for z in range(0,self.sides[2],4):
                u[((2,y,z),1)]=expv(np.array([eps,0.,0.]))
                u[((3,y+1,z),2)]=expv(np.array([0.,0.7*eps,0.]))
        return u
    def delta_prime_matrix(self,U,which):
        M=np.zeros((self.dim,self.dim))
        for p in self.plaquettes if which=='all' else self.plaq_in:
            x,mu,nu=p; bonds=self.edges_of(p); re,im=self._re_im(U,p)
            aa=np.zeros((4,12,2,2),complex)
            aa[0,6:9]=-np.array([P.rmap(U[(x,nu)],e) for e in E])
            aa[1,9:12]=-E; aa[2,0:3]=E
            aa[3,3:6]=np.array([P.rmap(U[(x,mu)],e) for e in E])
            c=aa.sum(axis=0)
            raw=-np.einsum('iab,jbc,ca->ij',c,c,re-I).real
            for r,s in itertools.combinations(range(4),2):
                raw+=(-1j*(np.einsum('iab,jbc,ca->ij',aa[r],aa[s],im)
                     -np.einsum('jab,ibc,ca->ij',aa[s],aa[r],im))).real
            gram=(raw+raw.T)/4
            ix=[3*self.bond_index[b]+j for b in bonds for j in range(3)]
            M[np.ix_(ix,ix)]+=gram
        return M
    def grad(self,U):
        d=np.zeros((self.dim,3*len(self.sites)))
        for i,(x,mu) in enumerate(self.bonds):
            j=self.site_index[x];k=self.site_index[self.shift(x,mu)]
            d[3*i:3*i+3,3*j:3*j+3]-=np.eye(3)
            d[3*i:3*i+3,3*k:3*k+3]+=adj3(U[(x,mu)])
        return d
    def path(self,x,dirs):
        ids=[]
        for mu in dirs:
            ids.append(self.bond_index[(x,mu)]);x=self.shift(x,mu)
        return ids
    def gamma(self,y,o): return self.path(y,[mu for mu in (2,1,0) for _ in range(o[mu])])
    def jsource(self,U):
        F={}
        for p in self.plaq_in:
            _,im=self._re_im(U,p)
            F[p]=im-np.trace(im)/2*I
        def f(x,nu,mu):
            if nu<mu:return F.get((x,nu,mu),P.Z2)
            return -F.get((x,mu,nu),P.Z2)
        J=[]
        for x,mu in self.bonds:
            val=np.zeros((2,2),complex)
            for nu in range(3):
                if nu==mu:continue
                y=self.shift(x,nu,-1);u=U[(y,nu)]
                val+=dagger(u)@f(y,nu,mu)@u-f(x,nu,mu)
            J.extend(coords(1j*val)) # JfS = -JSU2Loc = +i JfieldLoc at eta=1
        return np.array(J)[self.eidx]

class Raw:
    def __init__(self,lat,U):
        self.lat=lat;self.u=np.array([U[b] for b in lat.bonds])
        self.data=[]
        for c in lat.b1:
            x,mu=c; xp=lat.shift(x,mu,2)
            base=lat.path(x,[mu,mu]); legs=[]
            for o in lat.offs:
                xx=tuple(x[j]+o[j] for j in range(3))
                assert all(xx[j]<lat.sides[j] for j in range(3))
                legs.append((lat.gamma(x,o),lat.path(xx,[mu,mu]),lat.gamma(xp,o)))
            self.data.append((base,legs))
        self.bg=[self.blocked(self.u[None],d)[0] for d in self.data]
        self.q0=self.eval(np.zeros((1,lat.dim)))[0]
    @staticmethod
    def hol(v,path):
        h=np.broadcast_to(I,(len(v),2,2)).copy()
        for i in path:h=h@v[:,i]
        return h
    def blocked(self,v,d):
        base,legs=d;b=self.hol(v,base);s=np.zeros((len(v),3))
        for left,mid,right in legs:
            s+=logv(self.hol(v,left)@self.hol(v,mid)@dagger(self.hol(v,right))@dagger(b))/8
        return expv(s)@b
    def eval(self,A):
        v=expv(A.reshape(len(A),self.lat.nB,3))@self.u
        out=[]
        for d,bg in zip(self.data,self.bg):
            sm=np.zeros((len(v),3));sp=sm.copy()
            for left,_,right in d[1]:
                sm+=logv(self.hol(v,left)@dagger(self.hol(self.u[None],left)))/8
                sp+=logv(self.hol(v,right)@dagger(self.hol(self.u[None],right)))/8
            raw=expv(-sm)@self.blocked(v,d)@expv(sp)@dagger(bg)
            out.append(logv(raw)/2) # level-1 scaling ell^-1
        return np.stack(out,axis=1).reshape(len(A),-1)
    def jac(self,h):
        n=len(self.lat.eidx);J=np.zeros((len(self.lat.b1)*3,n))
        for start in range(0,n,48):
            ids=np.arange(start,min(n,start+48));A=np.zeros((len(ids),self.lat.dim))
            A[np.arange(len(ids)),self.lat.eidx[ids]]=h
            J[:,ids]=((self.eval(A)-self.eval(-A))/(2*h)).T
        return J
    def c2(self,A,h):
        return (self.eval(h*A[None])[0]+self.eval(-h*A[None])[0]-2*self.q0)/(2*h*h)


def assemble(lat,eps):
    U=lat.config(0,eps);raw=Raw(lat,U);n=len(lat.eidx)
    print('raw Jacobian',eps,flush=True)
    qtop=raw.jac(2e-5)
    emap={j:i for i,j in enumerate(lat.eidx)}
    q0=np.zeros((3*len(lat.b0),n))
    for i,b in enumerate(lat.b0):
        j=lat.bond_index[b]
        for c in range(3):q0[3*i+c,emap[3*j+c]]=1
    q=np.vstack([q0,qtop]);mass=q0.T@q0+2*qtop.T@qtop
    grad=lat.grad(U);lap=grad.T@grad
    qp=[];weights=[]
    for x in sorted(lat.lam0):
        block=np.zeros((3,lap.shape[0]));i=lat.site_index[x];block[:,3*i:3*i+3]=np.eye(3)
        qp.append(block);weights.extend([1.]*3)
    for y in sorted(lat.lam1):
        block=np.zeros((3,lap.shape[0]))
        for o in lat.offs:
            x=tuple(y[j]+o[j] for j in range(3));i=lat.site_index[x]
            trans=raw.hol(raw.u[None],lat.gamma(y,o))[0]
            block[:,3*i:3*i+3]=adj3(trans)/8
        qp.append(block);weights.extend([2.]*3)
    qp=np.vstack(qp);maskids=lat.sidx
    nq=null_space(qp[:,maskids],rcond=1e-10)
    ri=orth(lap[np.ix_(maskids,maskids)]@nq,rcond=1e-10)
    R=np.zeros_like(lap);R[np.ix_(maskids,maskids)]=ri@ri.T
    b=lap+qp.T@(np.array(weights)[:,None]*qp)
    gp=np.zeros_like(lap);gp[np.ix_(maskids,maskids)]=solve(b[np.ix_(maskids,maskids)],np.eye(len(maskids)),assume_a='pos')
    W=np.eye(lat.dim)[:,lat.eidx]-grad@gp@R@grad.T[:,lat.eidx]
    T=R@grad.T[:,lat.eidx]
    fixed=T.T@T+mass
    deltaIn=lat.delta_matrix(U,'in')
    loc=W.T@deltaIn@W+fixed;loc=(loc+loc.T)/2
    loc_ev=eigh(loc,eigvals_only=True)
    print('local eigen min',loc_ev[0],flush=True)
    if loc_ev[0]<1e-8:raise ValueError('local carrier lacks numerical positive gap')
    gq=solve(loc,q.T,assume_a='pos');N=q@gq
    nev=eigh(N,eigvals_only=True)
    if nev[0]<1e-9:raise ValueError('local compression lacks numerical positive gap')
    j=lat.jsource(U)
    hj=solve(N,gq.T@j,assume_a='pos')
    return raw,W,fixed,hj[len(q0):],dict(local_min=float(loc_ev[0]),N_min=float(nev[0]),
        q_rank=int(np.linalg.matrix_rank(q,tol=1e-8)),q_rows=q.shape[0],J_norm=float(np.linalg.norm(j)),
        HtJ_top_norm=float(np.linalg.norm(hj[len(q0):])),R_rank=ri.shape[1],raw_at_zero=float(np.max(np.abs(raw.q0))))


def run(eps):
    start=time.time();lat=Slab()
    raw,W,fixed,hj,checks=assemble(lat,eps)
    print('assembled',eps,checks,flush=True)
    def carrier(t):
        U=lat.config(t,eps)
        D=lat.delta_matrix(U,'all')
        M=W.T@D@W+fixed
        return (M+M.T)/2
    grid=[]
    def eigmin(t):
        v=float(eigh(carrier(t),eigvals_only=True,subset_by_index=[0,0])[0])
        grid.append([float(t),v]);print('theta, carrier min',t,v,flush=True);return v
    l=eigmin(0.);r=eigmin(np.pi)
    row=dict(eps=eps,checks=checks,root=None,grid=grid)
    if l>0 and r<0:
        root=brentq(eigmin,0.,np.pi,xtol=2e-10)
        M=carrier(root);ev,V=eigh(M,subset_by_index=[0,5])
        v=V[:,0];wv=W@v
        hs=[1e-2,3e-3,1e-3,3e-4,1e-4]
        forms=[]
        for h in hs:
            c=raw.c2(wv,h);forms.append(dict(h=h,C2_top_norm=float(np.linalg.norm(c)),v_Delta2_v=float(2*np.dot(hj,c))))
        # Deterministic unrelated directions check whether Delta2 is visible at all.
        rng=np.random.default_rng(731);random_forms=[]
        for _ in range(4):
            x=rng.normal(size=len(lat.eidx));x/=np.linalg.norm(x)
            random_forms.append(float(2*np.dot(hj,raw.c2(W@x,1e-3))))
        row.update(root=float(root),lowest_six=ev.tolist(),forms=forms,random_forms=random_forms)
        print('at carrier root',row,flush=True)
    row['seconds']=time.time()-start
    row['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return row

if __name__=='__main__':
    lat=Slab()
    # Independent local Gram check against retained Stage-A implementation at one plaquette background.
    U=lat.config(0.2,0.1)
    p0=lat.plaquettes;pin=lat.plaq_in
    lat.plaquettes=[p0[0],p0[21],p0[-1]]
    fast=lat.delta_prime_matrix(U,'all');slow=P.Lattice.delta_prime_matrix(lat,U,'all')
    assert np.max(np.abs(fast-slow))<1e-12
    lat.plaquettes=p0;lat.plaq_in=pin
    payload={'warning':'out-of-regime numerical assembly; no certified guard separation or headline refutation',
             'sides':lat.sides,'E_dimension':len(lat.eidx),'top_bonds':len(lat.b1),'gram_check':float(np.max(np.abs(fast-slow))), 'results':[]}
    for eps in [0.,0.08,0.16]:
        payload['results'].append(run(eps))
        (OUT/'assembled_results.json').write_text(json.dumps(payload,indent=2))
