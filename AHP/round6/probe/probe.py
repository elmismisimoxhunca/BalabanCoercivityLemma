#!/usr/bin/env python3
"""High-precision transcription of IVTR1.twistA/twistD (in ivt-r2 Attempt).
No Lean claims. See SOURCES.md and PROBE.md for the operator dictionary.
Only this directory is written; all RHS residuals use mpmath coefficients.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import sys
sys.dont_write_bytecode = True
import resource
resource.setrlimit(resource.RLIMIT_AS, (7*1024**3,7*1024**3))
import argparse, itertools, json, time
from pathlib import Path
from functools import lru_cache
import mpmath as mp
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu
OUT=Path(__file__).resolve().parent

def conj(x): return x.conjugate() if hasattr(x,'conjugate') else x

def clean(x):
    if isinstance(x,mp.mpc) and not x.imag: return x.real
    return x

def add(row,j,x):
    if x:
        v=clean(row.get(j,0)+x)
        if v: row[j]=v
        elif j in row: del row[j]

class Sp:
    def __init__(self,n,m): self.n=n;self.m=m;self.r=[{} for _ in range(n)]
    def put(self,i,j,v): add(self.r[i],j,v)
    def star(self):
        a=Sp(self.m,self.n)
        for i,row in enumerate(self.r):
            for j,v in row.items(): a.put(j,i,conj(v))
        return a
    def mul(self,b):
        assert self.m==b.n
        c=Sp(self.n,b.m)
        for i,row in enumerate(self.r):
            for k,v in row.items():
                for j,w in b.r[k].items(): add(c.r[i],j,v*w)
        return c
    def plus(self,b):
        a=Sp(self.n,self.m)
        for i in range(self.n):
            a.r[i]=self.r[i].copy()
            for j,v in b.r[i].items(): add(a.r[i],j,v)
        return a
    def apply(self,x):
        return [sum((v*x[j] for j,v in row.items()),0) for row in self.r]
    def scipy(self):
        rr=[];cc=[];vv=[]
        for i,row in enumerate(self.r):
            for j,v in row.items(): rr.append(i);cc.append(j);vv.append(complex(v))
        return coo_matrix((vv,(rr,cc)),shape=(self.n,self.m)).tocsc()
    def block(self,a,ro,co,scale=1):
        for i,row in enumerate(a.r):
            for j,v in row.items(): self.put(ro+i,co+j,scale*v)
    def sub(self,rows,cols):
        out=Sp(len(rows),len(cols));ci={j:k for k,j in enumerate(cols)}
        for k,i in enumerate(rows):
            for j,v in self.r[i].items():
                if j in ci: out.put(k,ci[j],v)
        return out

class Refine:
    """Double LU is only a preconditioner. Every residual uses mp data.
    Global residual stopping rule; tiny-tail reliability requires independent
    precision increases, not the rule alone. No interval enclosure claimed.
    """
    def __init__(self,A):
        self.A=A; self.lu=splu(A.scipy()); self.history=[]
    def solve(self,b):
        assert len(b)==self.A.n
        x=[mp.mpf(0)]*len(b);r=b[:];bn=max(map(abs,b),default=0)
        if not bn:return x
        tol=mp.power(10,-mp.mp.dps+8)
        hist=[]
        for k in range(2+mp.mp.dps//10):
            rn=max(map(abs,r)); hist.append(rn/bn)
            if rn/bn<tol:
                self.history.append(hist);return x
            d=self.lu.solve(np.array([complex(v/rn) for v in r]))
            x=[xi+rn*mp.mpc(float(di.real),float(di.imag)) for xi,di in zip(x,d)]
            ax=self.A.apply(x);r=[bi-ai for bi,ai in zip(b,ax)]
        raise ArithmeticError('refinement failed: '+str(hist))

# SU(2) jets along a charged real direction: g(t) has upper entries
# a0+a2*t^2 and b1*t. This stores EXACT Taylor coefficients, not differences.
# Multiplication follows [[a,b],[-conj(b),conj(a)]].
def prod(g,h):
    a,b,c=g; d,e,f=h
    return (a*d,a*e+b*conj(d),a*f+c*d-b*conj(e))
def dag(g): return (conj(g[0]),-g[1],conj(g[2]))
def expjet(s,z,c):
    if not s: return (mp.mpf(1),z,-abs(z)**2/2+1j*c)
    si=mp.sin(s);co=mp.cos(s)
    return (mp.mpc(co,si),si/s*z,(-si+1j*co)*c+abs(z)**2*(-si/(2*s)+1j*(s*co-si)/(2*s*s)))
def logjet(g):
    a,b,c=g; s=mp.arg(a)
    if not s:return (mp.mpf(0),b,mp.im(c))
    si=mp.sin(s);co=mp.cos(s)
    return (s,s/si*b,s/si*mp.im(c)+(s*co-si)/(si*si)*mp.re(c))
def jsum(a,b):return tuple(x+y for x,y in zip(a,b))
def jscale(a,c):return tuple(c*x for x in a)
ONE=(1,0,0)
ZERO=(0,0,0)

class Family:
    def __init__(self,q,R,eps,iy=0,iz=0,charge=1):
        self.q=q;self.R=R;self.eps=eps;self.charge=charge
        self.nx=q*(12*R+16);self.lo=4*q;self.hi=q*(12*R+12)
        self.p=q*(2*R+4);self.s=q*(10*R+12)
        self.ph=(mp.exp(2j*mp.pi*iy/(4*q)),mp.exp(2j*mp.pi*iz/(4*q)))
        self.sites=list(itertools.product(range(self.nx),range(2),range(2)))
        self.si={s:i for i,s in enumerate(self.sites)}
        self.bonds=[(x,d) for x in self.sites for d in range(3)]
        self.bi={b:i for i,b in enumerate(self.bonds)}
        self.e=[i for i,b in enumerate(self.bonds) if self.in0(b[0]) or self.in0(self.shift(*b))]
        self.em={j:i for i,j in enumerate(self.e)};self.n=len(self.e)
        self.b0=[b for b in self.bonds if (self.lam0(b[0]) or self.lam0(self.shift(*b))) and not(self.in1(b[0]) or self.in1(self.shift(*b)))]
        self.b1=[((x,0,0),d) for x in range(self.p-2,self.s,2) for d in range(3) if x>=self.p or d==0]
        self.offsets=list(itertools.product(range(2),repeat=3))
        self.rawdata={b:self.paths(b) for b in self.b1}
    def shift(self,x,d,n=1):
        a=list(x);a[d]+=n;return tuple(a)
    def in0(self,x):return self.lo<=x[0]<self.hi
    def in1(self,x):return self.p<=x[0]<self.s
    def lam0(self,x):return self.in0(x) and not self.in1(x)
    def canonical(self,x):return (x[0]%self.nx,x[1]%2,x[2]%2)
    def index(self,x,d=None):
        y=self.canonical(x);p=self.ph[0]**(x[1]//2)*self.ph[1]**(x[2]//2)
        return (self.si[y] if d is None else self.bi[(y,d)]),p
    def angle(self,b,t=0):
        x,d=b;y=self.shift(x,d)
        if not(self.in0(x) or self.in0(y)):return t
        return self.eps if x[0]==self.p and x[1]%2==0 and x[2]%2==0 and d==1 else 0
    def path(self,x,dirs):
        p=[]
        for d in dirs:p.append((x,d));x=self.shift(x,d)
        return p
    def gamma(self,x,o):return self.path(x,[d for d in (2,1,0) for _ in range(o[d])])
    def paths(self,b):
        x,d=b;xp=self.shift(x,d,2)
        return (self.path(x,[d,d]),[(self.gamma(x,o),self.path(tuple(x[j]+o[j] for j in range(3)),[d,d]),self.gamma(xp,o)) for o in self.offsets])
    def rawjet(self,b,field):
        # R2Raw1.lean:36-78, R2RawX.lean:187, ZXR2Sector.lean:97,109.
        base,legs=self.rawdata[b]
        @lru_cache(None)
        def link(e):
            z=field.get(e,0);u=mp.exp(1j*self.angle(e))
            return (u,z*conj(u),-abs(z)**2*u/2)
        def hol(path):
            a=ONE
            for e in path:a=prod(a,link(e))
            return a
        def bg(path):return (mp.exp(1j*sum(self.angle(e) for e in path)),0,0)
        B=hol(base);S=ZERO;sm=ZERO;sp=ZERO
        for l,m,r in legs:
            L=hol(l);M=hol(m);rr=hol(r)
            S=jsum(S,jscale(logjet(prod(prod(prod(L,M),dag(rr)),dag(B))),mp.mpf(1)/8))
            sm=jsum(sm,jscale(logjet(prod(L,dag(bg(l)))),mp.mpf(1)/8))
            sp=jsum(sp,jscale(logjet(prod(rr,dag(bg(r)))),mp.mpf(1)/8))
        blocked=prod(expjet(*S),B)
        background=mp.exp(1j*(S[0]+sum(self.angle(e) for e in base)))
        word=prod(prod(prod(expjet(*jscale(sm,-1)),blocked),expjet(*sp)),(conj(background),0,0))
        return jscale(logjet(word),mp.mpf(1)/2)
    def qmatrix(self):
        Q=Sp(len(self.b0)+len(self.b1),self.n)
        for i,b in enumerate(self.b0):Q.put(i,self.em[self.bi[b]],1)
        for i,b in enumerate(self.b1,len(self.b0)):
            base,legs=self.rawdata[b];used=set(base)
            for l,m,r in legs:used.update(l+m+r)
            curved=self.charge and any(self.angle(e) for e in used)
            if curved:
                for e in used:
                    j,ph=self.index(*e)
                    if j in self.em: Q.put(i,self.em[j],self.rawjet(b,{e:1})[1]*ph)
            else:
                for l,m,r in legs:
                    for e in m:
                        j,ph=self.index(*e)
                        if j in self.em:Q.put(i,self.em[j],mp.mpf(1)/16*ph)
        return Q
    def grad_and_kernel(self):
        grad=Sp(len(self.bonds),len(self.sites))
        for i,(x,d) in enumerate(self.bonds):
            j,_=self.index(x);k,ph=self.index(self.shift(x,d))
            grad.put(i,j,-1);grad.put(i,k,ph*mp.exp(2j*self.charge*self.angle((x,d))))
        N=Sp(len(self.sites),7*((self.s-self.p)//2));col=0
        for x in range(self.p,self.s,2):
            y=(x,0,0);base=[]
            for o in self.offsets:
                z=tuple(y[j]+o[j] for j in range(3));k,_=self.index(z)
                tr=mp.exp(2j*self.charge*sum(self.angle(e) for e in self.gamma(y,o)))
                base.append((k,tr))
            ref,rt=base[-1]
            for k,tr in base[:-1]:N.put(k,col,1);N.put(ref,col,-tr/rt);col+=1
        return grad,N
    def plaq(self,which='in',t=0):
        D=Sp(len(self.bonds),len(self.bonds));J=[mp.mpf(0)]*len(self.bonds)
        for x in self.sites:
            for mu,nu in [(0,1),(0,2),(1,2)]:
                xm=self.shift(x,mu);xn=self.shift(x,nu)
                edges=[(x,mu),(xm,nu),(xn,mu),(x,nu)]
                inside=all(self.in0(y) for y in [x,xm,xn,self.shift(xm,nu)])
                if (which=='in' and not inside) or (which=='out' and inside):continue
                if not any(self.index(*e)[0] in self.em for e in edges):continue
                ang=[self.angle(e,t) for e in edges]
                h=ang[0]+ang[1]-ang[2]-ang[3]
                co=mp.cos(h);si=mp.sin(h)
                cs=[1,mp.exp(2j*self.charge*ang[0]),-mp.exp(2j*self.charge*ang[3]),-1]
                ids=[];phase=[]
                for e in edges:
                    j,ph=self.index(*e);ids.append(j);phase.append(ph)
                mat=[[co*conj(cs[i])*cs[j] for j in range(4)] for i in range(4)]
                if self.charge and si:
                    for r,s in itertools.combinations([2,3,0,1],2):
                        v=-1j*si*conj(cs[r])*cs[s]
                        mat[r][s]+=v;mat[s][r]+=conj(v)
                for i in range(4):
                    for j in range(4):D.put(ids[i],ids[j],conj(phase[i])*mat[i][j]*phase[j])
                if which=='in':
                    for j,sgn in enumerate([1,1,-1,-1]):J[ids[j]]+=sgn*si
        return D,J
    def assemble(self):
        start=time.time();grad,N=self.grad_and_kernel();Q=self.qmatrix()
        G=grad.mul(N);L=grad.star().mul(G)
        for i,x in enumerate(self.sites):
            if not self.in0(x):L.r[i]={}
        H=L.star().mul(L);F=L.star().mul(grad.star().sub(range(len(self.sites)),self.e))
        delta,jfull=self.plaq();de=delta.sub(self.e,range(len(self.bonds)))
        K=delta.sub(self.e,self.e)
        weights=[1]*len(self.b0)+[2]*len(self.b1)
        for row,w in zip(Q.r,weights):
            for i,a in row.items():
                for j,b in row.items():K.put(i,j,w*conj(a)*b)
        V=de.mul(G);Z=G.star().mul(delta.mul(G));n=self.n;h=H.n
        Aug=Sp(n+2*h,n+2*h)
        for block,ro,co,sgn in [(K,0,0,1),(V,0,n,-1),(V.star(),n,0,-1),(F, n+h,0,-1),(F.star(),0,n+h,-1),(Z.plus(H),n,n,1),(H,n,n+h,1),(H,n+h,n,1)]:Aug.block(block,ro,co,sgn)
        self.G=G;self.H=H;self.F=F;self.Q=Q;self.K=K;self.V=V;self.Z=Z;self.aug=Aug
        self.j=[jfull[i] for i in self.e]
        self.boundary=[i for i,j in enumerate(self.e) if self.bonds[j][0][0] in [self.lo-1,self.lo,self.hi-1] and (self.bonds[j][0][0]!=self.lo or self.bonds[j][1]!=0) and (self.bonds[j][0][0]!=self.hi-1 or self.bonds[j][1]==0)]
        # Boundary includes longitudinal incoming/outgoing and transverse at lo;
        # outgoing plaquettes also contain transverse bonds at hi-1.
        out,_=self.plaq('out',0)
        self.boundary=sorted({self.em[j] for i,row in enumerate(out.r) for j in row if j in self.em and i in self.em})
        self.assembly_seconds=time.time()-start
        print('assembled',self.q,self.R,self.charge,'n',n,'aug',Aug.n,'nnz',sum(map(len,Aug.r)),'seconds',self.assembly_seconds,flush=True)
        return self
    def boundary_inverse(self):
        self.solver=Refine(self.aug);X=[]
        for k,i in enumerate(self.boundary):
            rhs=[0]*self.aug.n;rhs[i]=1;X.append(self.solver.solve(rhs))
            print('boundary column',k+1,'/',len(self.boundary),flush=True)
        self.X=X
        C=mp.matrix([[col[i] for col in X] for i in self.boundary]);self.C=(C+C.H)/2
        self.S=self.C**-1
        return self.S
    def theta(self,t):
        out,_=self.plaq('out',t)
        e=[self.e[i] for i in self.boundary]
        dd=out.sub(e,e)
        return mp.matrix([[dd.r[i].get(j,0) for j in range(len(e))] for i in range(len(e))])
    def dressed(self,v,u):
        w=[mp.mpc(0)]*len(self.bonds)
        for i,j in enumerate(self.e):w[j]=v[i]
        gu=self.G.apply(u)
        return [a-b for a,b in zip(w,gu)]
    def hj(self):
        assert self.charge==0
        # Exact KKT [Aug Q*; Q 0] gives multiplier H*J. No compressed inverse.
        a=self.aug;n=a.n;Q=self.Q;k=Q.n
        sys=Sp(n+k,n+k);sys.block(a,0,0);sys.block(Q,n,0);sys.block(Q.star(),0,n)
        solve=Refine(sys);rhs=self.j+[0]*(n+k-self.n)
        x=solve.solve(rhs)
        return x[n+len(self.b0):],solve.history[-1][-1]
    def correction(self,w,hj):
        total=mp.mpf(0);terms=[]
        for b,h in zip(self.b1,hj):
            base,legs=self.rawdata[b];used=set(base)
            for l,m,r in legs:used.update(l+m+r)
            f={e:w[self.index(*e)[0]]*self.index(*e)[1] for e in used}
            c=self.rawjet(b,f)[2];terms.append(2*mp.re(h)*c);total+=terms[-1]
        return total,terms

def fmt(x):return mp.nstr(x,mp.mp.dps-5)
def jsonable(x):
    if isinstance(x,(mp.mpf,mp.mpc)):return fmt(x)
    if isinstance(x,dict):return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [jsonable(v) for v in x]
    return x

def run(q,R,estr,dps,iy=0,iz=0):
    mp.mp.dps=dps;eps=mp.mpf(estr);start=time.time()
    f=Family(q,R,eps,iy,iz,1).assemble();S=f.boundary_inverse()
    # Cache only the small exterior matrix: it is exactly independent of eps.
    def eig(t,vectors=False):
        ev,V=mp.eighe(S+f.theta(t));return (ev,V) if vectors else ev[0]
    a=mp.mpf('.5');b=mp.mpf('.7')
    assert eig(0)>0 and eig(a)>0 and eig(b)<0
    # Secant/Newton on the lowest eigenvalue, with a bracket sanity check.
    t=mp.findroot(lambda x: eig(x),(a,b),solver='secant',tol=mp.power(10,-dps+15),verify=False)
    vals,V=eig(t,True);bv=V[:,0];rho=S*bv
    full=[sum(f.X[k][i]*rho[k] for k in range(len(f.X))) for i in range(f.aug.n)]
    norm=mp.sqrt(sum(abs(v)**2 for v in full[:f.n]));full=[x/norm for x in full]
    v=full[:f.n];u=full[f.n:f.n+f.H.n];w=f.dressed(v,u)
    residual=f.aug.apply(full);th=f.theta(t);bv=mp.matrix([v[i] for i in f.boundary]);tv=th*bv
    for k,i in enumerate(f.boundary):residual[i]+=tv[k]
    neutral=Family(q,R,eps,0,0,0).assemble();hj,hjres=neutral.hj()
    pairing,terms=f.correction(w,hj)
    # Quadratic form on the SAME unit vector just before the crossing.
    # This detects corrected negativity, but does not by itself certify PD.
    step=mp.mpf('1e-6')
    slope=mp.re((bv.H*(f.theta(t+step)-f.theta(t-step))*bv)[0]/(2*step))
    dt=abs(pairing)/(2*abs(slope))
    t1=t-dt;atheta=f.theta(t1)
    carrier_form=mp.re((bv.H*(atheta-th)*bv)[0])
    before_eigs,_=mp.eighe(S+atheta)
    fold_weights=[]
    for ky,kz in itertools.product(range(2),repeat=2):
        weight=mp.mpf(0)
        for x in range(f.lo-1,f.hi):
            for mu in range(3):
                amp=sum(((-1)**(ky*y+kz*z)*mp.exp(-1j*(mp.arg(f.ph[0])*y+mp.arg(f.ph[1])*z)/2)*v[f.em[f.bi[((x,y,z),mu)]]] if f.bi[((x,y,z),mu)] in f.em else 0) for y,z in itertools.product(range(2),repeat=2))/2
                weight+=abs(amp)**2
        fold_weights.append([ky,kz,weight])
    tail_x=f.lo+8;tail=[]
    for mu in range(3):
        z0=v[f.em[f.bi[((tail_x,0,0),mu)]]];z1=v[f.em[f.bi[((tail_x+1,0,0),mu)]]]
        tail.append([mu,z0,z1/z0 if z0 else 0])
    result=dict(q=q,R=R,epsilon=estr,dps=dps,sector=[iy,iz],carrier_complex_dimension=f.n,
        folded_fine_fourier_weights=fold_weights,collar_successive_ratios=tail,
        boundary_dimension=len(f.boundary),root=t,schur_eigenvalues=list(vals),
        kernel_real_dimension_in_this_sector=2,
        longitudinal_mass_centroid=sum(abs(v[i])**2*f.bonds[j][0][0] for i,j in enumerate(f.e)),
        left_half_mass=sum(abs(v[i])**2 for i,j in enumerate(f.e) if f.bonds[j][0][0] < (f.lo+f.hi)/2),
        augmented_kernel_max_residual=max(map(abs,residual)),
        HtJ_solve_relative_residual=hjres,pairing=pairing,pairing_terms=terms,
        initial_boundary_schur_min=eig(0),pairing_slope=slope,alternative_offset=dt,
        pre_crossing_schur_grid=[(mp.mpf(k)/10*t,eig(mp.mpf(k)/10*t)) for k in range(10)],
        alternative_carrier_test_form=carrier_form,alternative_corrected_test_form=carrier_form-pairing,
        alternative_boundary_schur_min=before_eigs[0],
        initial_PSD_status='not certified: boundary Schur is positive; B positivity and all sectors need separate checking',
        initial_corrected_PSD_status='not checked',seconds=time.time()-start,
        peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    fn=OUT/f'q{q}_R{R}_e{estr}_p{dps}_s{iy}_{iz}.json'
    fn.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('RESULT',fn,'pairing',fmt(pairing),'root',fmt(t),'seconds',result['seconds'],flush=True)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=18)
    p.add_argument('--eps',default='1e-3');p.add_argument('--dps',type=int,default=70)
    p.add_argument('--iy',type=int,default=0);p.add_argument('--iz',type=int,default=0)
    a=p.parse_args();run(a.q,a.R,a.eps,a.dps,a.iy,a.iz)
