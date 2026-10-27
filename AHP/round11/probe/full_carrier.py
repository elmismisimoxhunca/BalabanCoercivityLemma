#!/usr/bin/env python3
"""Full (not boundary-Schur) massless/with-mass Ginv spectra, flat-touch slab.
Compact float transcription of round6/probe/probe.py Family, eps=0, q=1.
Uses the complete longitudinal extent, two-site transverse Bloch cells,
all 16 characters and both neutral/charged SU(2) sectors. W and T are
applied explicitly via the N(Q') basis, not dropped from the computation.
No inverse of Ginv, G1inv or genFormS is computed. Evidence only.
"""
import os,sys,resource
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
sys.dont_write_bytecode=True
resource.setrlimit(resource.RLIMIT_AS,(1800*1024**2,1800*1024**2))
from pathlib import Path
import itertools,json,time
import numpy as np
from scipy.sparse import coo_matrix,diags
from scipy.sparse.linalg import splu,LinearOperator,eigsh
OUT=Path(__file__).resolve().parent

def sp(n,m,entries):
    if not entries:return coo_matrix((n,m),dtype=complex).tocsc()
    rr,cc,vv=zip(*entries)
    return coo_matrix((vv,(rr,cc)),shape=(n,m),dtype=complex).tocsc()

class Full:
    def __init__(self,iy,iz,charge,R=18,q=1):
        self.nx=q*(12*R+16);self.lo=4*q;self.hi=q*(12*R+12)
        self.p=q*(2*R+4);self.s=q*(10*R+12);self.charge=charge
        self.ph=np.exp(2j*np.pi*np.array([iy,iz])/(4*q))
        self.sites=list(itertools.product(range(self.nx),range(2),range(2)))
        self.si={x:i for i,x in enumerate(self.sites)}
        self.bonds=[(x,d) for x in self.sites for d in range(3)]
        self.bi={b:i for i,b in enumerate(self.bonds)}
        self.e=[i for i,(x,d) in enumerate(self.bonds) if self.in0(x) or self.in0(self.shift(x,d))]
        self.em={j:i for i,j in enumerate(self.e)};self.n=len(self.e)
        self.E=sp(len(self.bonds),self.n,[(j,i,1) for i,j in enumerate(self.e)])
        # U=1 on all bonds read by grad N, lap N and every averaging row.
        g=[]
        for i,(x,d) in enumerate(self.bonds):
            j,_=self.index(x);k,ph=self.index(self.shift(x,d))
            g.extend([(i,j,-1),(i,k,ph)])
        grad=sp(len(self.bonds),len(self.sites),g)
        offs=list(itertools.product(range(2),repeat=3));entries=[];col=0
        for x in range(self.p,self.s,2):
            ids=[self.index((x+o[0],o[1],o[2]))[0] for o in offs]
            for k in ids[:-1]:entries.extend([(k,col,1),(ids[-1],col,-1)]);col+=1
        N=sp(len(self.sites),col,entries);G=grad@N
        mask=diags([int(self.in0(x)) for x in self.sites],dtype=float)
        L=mask@grad.conj().T@G;H=(L.conj().T@L).tocsc()
        F=(L.conj().T@grad.conj().T@self.E).tocsc()
        self.G=G;self.F=F;self.lu=splu(H)
        # G' R = N H^{-1} L*: since Q' N=0, (lap+Q'*aQ')N=L
        # for every a>0. Thus W=E-G H^{-1}F, T*T=F*H^{-1}F.
        b0=[(x,d) for x,d in self.bonds if (self.lam0(x) or self.lam0(self.shift(x,d)))
             and not(self.in1(x) or self.in1(self.shift(x,d)))]
        b1=[((x,0,0),d) for x in range(self.p-2,self.s,2) for d in range(3) if x>=self.p or d==0]
        entries=[(i,self.em[self.bi[b]],1) for i,b in enumerate(b0)]
        for i,(x,d) in enumerate(b1,len(b0)):
            for o in offs:
                y=tuple(x[j]+o[j] for j in range(3))
                for step in range(2):
                    z=list(y);z[d]+=step;j,ph=self.index(tuple(z),d)
                    if j in self.em:entries.append((i,self.em[j],ph/16))
        Q=sp(len(b0)+len(b1),self.n,entries)
        self.mass=Q.conj().T@diags([1]*len(b0)+[2]*len(b1),dtype=float)@Q

    def in0(self,x):return self.lo<=x[0]<self.hi
    def in1(self,x):return self.p<=x[0]<self.s
    def lam0(self,x):return self.in0(x) and not self.in1(x)
    def shift(self,x,d):
        y=list(x);y[d]+=1;return tuple(y)
    def index(self,x,d=None):
        y=(x[0]%self.nx,x[1]%2,x[2]%2)
        ph=self.ph[0]**(x[1]//2)*self.ph[1]**(x[2]//2)
        return (self.si[y] if d is None else self.bi[(y,d)]),ph
    def angle(self,e,t):
        x,d=e
        return 0. if self.in0(x) or self.in0(self.shift(x,d)) else t
    def delta(self,t):
        entries=[]
        for x in self.sites:
            for mu,nu in [(0,1),(0,2),(1,2)]:
                xm,xn=self.shift(x,mu),self.shift(x,nu)
                if not any(self.in0(v) for v in [x,xm,xn,self.shift(xm,nu)]):continue
                edges=[(x,mu),(xm,nu),(xn,mu),(x,nu)]
                ang=[self.angle(e,t) for e in edges];h=ang[0]+ang[1]-ang[2]-ang[3]
                c=np.array([1,np.exp(2j*self.charge*ang[0]),-np.exp(2j*self.charge*ang[3]),-1])
                mat=np.cos(h)*np.outer(c.conj(),c)
                if self.charge:
                    for r,s in itertools.combinations([2,3,0,1],2):
                        v=-1j*np.sin(h)*c[r].conjugate()*c[s]
                        mat[r,s]+=v;mat[s,r]+=v.conjugate()
                ids,ph=zip(*(self.index(*e) for e in edges))
                for i in range(4):
                    for j in range(4):entries.append((ids[i],ids[j],ph[i].conjugate()*mat[i,j]*ph[j]))
        return sp(len(self.bonds),len(self.bonds),entries)
    def carrier(self,t,a):
        D=self.delta(t);F=self.F;G=self.G;E=self.E;solve=self.lu.solve
        def apply(x):
            u=solve(F@x);w=E@x-G@u;dw=D@w
            return E.conj().T@dw-F.conj().T@solve(G.conj().T@dw)+F.conj().T@u+a*(self.mass@x)
        A=LinearOperator((self.n,self.n),matvec=apply,dtype=complex)
        # Exact flat-touch algebra predicts Delta G = 0. Check it numerically
        # but still retain every W term in apply().
        dg=D@G
        dgmax=float(np.max(abs(dg.data),initial=0))
        rng=np.random.default_rng(97);v0=rng.normal(size=self.n)+1j*rng.normal(size=self.n)
        w,v=eigsh(A,k=1,which='SA',v0=v0,tol=2e-9,maxiter=5000,ncv=40)
        v=v[:,0];value=float(w[0]);candidate=value;null_used=False
        if a==0 and value>0:
            # Known local gauge null vector missed by a degenerate Krylov solve.
            phi=np.zeros(len(self.sites),complex);phi[self.si[(self.lo+2,0,0)]]=1
            grad_entries=[]
            for j in self.e:
                x,d=self.bonds[j];i,_=self.index(x);k,ph=self.index(self.shift(x,d))
                grad_entries.append(ph*phi[k]-phi[i])
            v=np.array(grad_entries);v/=np.linalg.norm(v)
            assert np.linalg.norm(apply(v))<1e-10
            value=0.;null_used=True
        res=float(np.linalg.norm(apply(v)-value*v))
        return {'lambda_min':value,'residual':res,'delta_gradN_max_entry':dgmax,'dimension_complex':self.n,
                'arpack_candidate':candidate,'explicit_null_used':null_used}

def main():
    start=time.time();rows=[]
    # theta=pi full character screen at a=0 (mass removed),8,9,20;
    # zero-character angle sweep corroborates the actual non-Cartan carrier.
    for charge in [0,1]:
        for iy in range(4):
            for iz in range(4):
                f=Full(iy,iz,charge)
                cases=[(np.pi,a) for a in [0,8,9,20]]
                if iy==iz==0:cases += [(t,0) for t in [np.pi/4,np.pi/2,3*np.pi/4]]
                for t,a in cases:
                    row={'charge':charge,'iy':iy,'iz':iz,'theta':t,'mass_coefficient':a,**f.carrier(t,a)}
                    rows.append(row)
                print('full',charge,iy,iz,[(r['mass_coefficient'],r['lambda_min']) for r in rows[-len(cases):]],flush=True)
    result={'status':'full carrier numerical spectra, not a theorem or genFormS proof',
            'geometry':{'q':1,'R':18,'ell':2,'M':2,'k':1,'fine_sides':[232,8,8]},
            'rows':rows,'pi_summary':[],'seconds':time.time()-start,
            'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    for a in [0,8,9,20]:
        rr=[r for r in rows if r['theta']==np.pi and r['mass_coefficient']==a]
        result['pi_summary'].append({'a':a,'min':min(r['lambda_min'] for r in rr),
            'max_residual':max(r['residual'] for r in rr),'all_32_characters':len(rr)==32})
    (OUT/'full_carrier.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['pi_summary','seconds','peak_rss_kib']},indent=2))
if __name__=='__main__':main()
