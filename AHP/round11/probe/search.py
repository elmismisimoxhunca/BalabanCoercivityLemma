#!/usr/bin/env python3
"""Evidence only. Source-normalized Delta, compressed to an outer collar.
This is a restriction of the actual carrier (W=id,T=0 on this collar), not
an inverse of a compressed operator and not a simulation of genFormS.
Only AHP/round11/probe is written. See PROBE.md for the embedding/dictionary.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import sys
sys.dont_write_bytecode = True
import resource
resource.setrlimit(resource.RLIMIT_AS, (1800*1024**2, 1800*1024**2))
import itertools, json, time
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh
from scipy.optimize import minimize_scalar
OUT = Path(__file__).resolve().parent
PAIRS = [(0,1),(0,2),(1,2)]
ORDER = [2,3,0,1]  # ZW,WX,XY,YZ; frozen DeltaPrimeOperator.secondBilPlaq.

def shift(x,mu,n):
    y=list(x); y[mu]+=1
    if mu: y[mu] %= n
    return tuple(y)

class Collar:
    """Omega0 is x>=0 locally. Embed this LEFT boundary in dilTower(q,18).
    Supported bonds: incoming normal at x=-1, all directions 0<=x<width.
    width<=8, n=8q: safely separated from Omega1, which starts at x=36q.
    """
    def __init__(self,n,width,normal_only=False):
        self.n=n; self.width=width; self.normal_only=normal_only
        self.bonds=[((x,y,z),d) for x in range(-1,width)
                    for y in range(n) for z in range(n) for d in range(3)
                    if (x>=0 or d==0) and (not normal_only or x==-1)]
        self.bi={b:i for i,b in enumerate(self.bonds)}
        self.plaqs=[]
        for x in range(-2,width+1):
            for y in range(n):
                for z in range(n):
                    p=(x,y,z)
                    for mu,nu in PAIRS:
                        pm,pn=shift(p,mu,n),shift(p,nu,n)
                        edges=[(p,mu),(pm,nu),(pn,mu),(p,nu)]
                        corners=[p,pm,pn,shift(pm,nu,n)]
                        if not any(v[0]>=0 for v in corners):continue
                        ids=[self.bi.get(e,-1) for e in edges]
                        if all(i<0 for i in ids):continue
                        self.plaqs.append((edges,ids))
        self.boundary_ids=[i for i,(x,d) in enumerate(self.bonds) if x[0]==-1 or (x[0]==0 and d!=0)]

    def assemble(self,angles,charge):
        # All nontrivial links actually read are tangential links on x=-1.
        rr=[];cc=[];vv=[]
        for edges,ids in self.plaqs:
            ang=[angles[d-1,x[1],x[2]] if x[0]<0 and d else 0. for x,d in edges]
            h=ang[0]+ang[1]-ang[2]-ang[3]
            co,si=np.cos(h),np.sin(h)
            cs=np.array([1,np.exp(2j*charge*ang[0]),-np.exp(2j*charge*ang[3]),-1])
            mat=co*np.outer(cs.conj(),cs)
            if charge:
                for r,s in itertools.combinations(ORDER,2):
                    v=-1j*si*cs[r].conjugate()*cs[s]
                    mat[r,s]+=v;mat[s,r]+=v.conjugate()
            for i in range(4):
                if ids[i]<0:continue
                for j in range(4):
                    if ids[j]<0:continue
                    rr.append(ids[i]);cc.append(ids[j]);vv.append(mat[i,j])
        return coo_matrix((vv,(rr,cc)),shape=(len(self.bonds),)*2).tocsr()

    def eigen(self,angles,charge,vector=False):
        A=self.assemble(angles,charge)
        # Deterministic nonconstant start avoids missing high-frequency modes.
        rng=np.random.default_rng(7721)
        v0=rng.normal(size=A.shape[0])+1j*rng.normal(size=A.shape[0])
        w,v=eigsh(A,k=1,which='SA',tol=2e-11,maxiter=4000,v0=v0)
        value=float(w[0]);v=v[:,0];candidate=value;null_used=False
        # ARPACK can miss a highly multiple exact zero eigenspace. An interior
        # site gradient is an exact null vector for every exterior background.
        if not self.normal_only and self.width>=2 and value>0:
            site=(1,0,0)
            v=np.array([float(shift(x,d,self.n)==site)-float(x==site) for x,d in self.bonds],complex)
            v/=np.linalg.norm(v)
            assert np.linalg.norm(A@v)<1e-10
            value=0.;null_used=True
        if self.normal_only and value>0:
            # This small matrix can be checked densely without a nullspace assumption.
            ww,vv=np.linalg.eigh(A.toarray());value=float(ww[0]);v=vv[:,0]
        residual=float(np.linalg.norm(A@v-value*v))
        result={'lambda_min':value,'residual':residual,'dimension_complex':A.shape[0],
                'arpack_candidate':candidate,'explicit_null_used':null_used,
                'boundary_norm_squared':float(np.sum(abs(v[self.boundary_ids])**2))}
        if vector:return result,v
        return result

def uniform(n,t):return np.full((2,n,n),t)

def matrix_formula_audit():
    """Independent direct 2x2 trace vs charged/neutral transcription."""
    E=np.array([[[1j,0],[0,-1j]],[[0,1],[-1,0]],[[0,1j],[1j,0]]])
    rng=np.random.default_rng(618)
    worst=0.;local_min=0.;local_max=0.
    for _ in range(50):
        ang=rng.uniform(-np.pi,np.pi,4);h=ang@[1,1,-1,-1]
        U=np.diag([np.exp(1j*h),np.exp(-1j*h)])
        co,si=np.cos(h),np.sin(h)
        vals=rng.normal(size=(4,3));X=np.einsum('ra,aij->rij',vals,E)
        u0=np.diag([np.exp(1j*ang[0]),np.exp(-1j*ang[0])])
        u3=np.diag([np.exp(1j*ang[3]),np.exp(-1j*ang[3])])
        A=[X[0],u0@X[1]@u0.conj().T,-u3@X[2]@u3.conj().T,-X[3]]
        curl=sum(A);herm=1j*curl
        raw_first=np.trace(herm@herm@((U+U.conj().T)/2-np.eye(2))).real/2
        comm=sum((1j*((1j*A[r])@(1j*A[s])-(1j*A[s])@(1j*A[r]))
                  for r,s in itertools.combinations(ORDER,2)))
        raw_second=np.trace(comm@((U-U.conj().T)/(2j))).real/2
        raw=-np.trace(curl@curl).real/2+raw_first+raw_second
        calc=0.
        for charge in [0,1]:
            cs=np.array([1,np.exp(2j*charge*ang[0]),-np.exp(2j*charge*ang[3]),-1])
            H=co*np.outer(cs.conj(),cs)
            if charge:
                for r,s in itertools.combinations(ORDER,2):
                    z=-1j*si*cs[r].conjugate()*cs[s]
                    H[r,s]+=z;H[s,r]+=z.conjugate()
            x=vals[:,0] if charge==0 else vals[:,1]+1j*vals[:,2]
            calc+=(x.conj()@H@x).real
            ev=np.linalg.eigvalsh(H);local_min=min(local_min,ev[0]);local_max=max(local_max,ev[-1])
        worst=max(worst,abs(calc-raw))
    assert worst<1e-10
    return {'random_plaquettes':50,'max_trace_formula_error':worst,
            'sample_local_eigen_range':[local_min,local_max]}

def main():
    start=time.time();result={'status':'numerical evidence, not Lean or interval-certified',
        'mass_note':'On these collar fields actual Ginv form is Delta + a*I.',
        'geometry':{'ell':2,'k':1,'R':18,'q_values':[1,2],
            'fine_sides':'(232q,8q,8q)','Omega0':'[4q,228q)','Omega1':'[40q,192q)',
            'M':'2q','embedding':'left collar translated by +4q; no opposite-boundary coupling'},
        'memory_cap_bytes':1800*1024**2,'audit':matrix_formula_audit(),'normal_only':[],
        'uniform_grid':[],'width_convergence':[],'patterns':[],'optimizations':[]}
    for n in [8,16,24]:
        C=Collar(n,1,True)
        for t in [0.,np.pi/2,np.pi]:
            for charge in [0,1]:
                row={'n':n,'theta':t,'charge':charge,**C.eigen(uniform(n,t),charge)}
                result['normal_only'].append(row)
                if t==np.pi:assert abs(row['lambda_min']+8)<1e-8
    C=Collar(8,4)
    for t in np.linspace(0,np.pi,17):
        for charge in [0,1]:
            row={'n':8,'width':4,'theta':float(t),'charge':charge,**C.eigen(uniform(8,t),charge)}
            result['uniform_grid'].append(row)
        print('uniform',t,result['uniform_grid'][-2]['lambda_min'],result['uniform_grid'][-1]['lambda_min'],flush=True)
    for charge in [0,1]:
        obj=lambda t:C.eigen(uniform(8,t),charge)['lambda_min']
        opt=minimize_scalar(obj,bounds=(np.pi/2,np.pi),method='bounded',options={'xatol':1e-7})
        result['optimizations'].append({'scope':'local bounded optimizer; not a global certificate',
            'charge':charge,'theta':float(opt.x),'success':bool(opt.success),
            **C.eigen(uniform(8,opt.x),charge)})
    for n in [8,16]:
        for width in [1,2,4,8]:
            C=Collar(n,width)
            for t in [np.pi, result['optimizations'][1]['theta']]:
                for charge in [0,1]:
                    result['width_convergence'].append({'n':n,'width':width,'theta':t,'charge':charge,
                        **C.eigen(uniform(n,t),charge)})
    C=Collar(8,4);rng=np.random.default_rng(72917);yy,zz=np.indices((8,8))
    for name in ['checkerboard','stripe','opposite','single_link','random_0pi','random_angles']:
        reps=5 if name.startswith('random') else 1
        for rep in range(reps):
            for t in ([np.pi/2,np.pi] if not name.startswith('random') else [np.pi]):
                a=uniform(8,t)
                if name=='checkerboard':a[:]*=(-1.)**(yy+zz)
                if name=='stripe':a[:]*=(-1.)**yy
                if name=='opposite':a[1]*=-1
                if name=='single_link':a[:]=0.;a[0,0,0]=t
                if name=='random_0pi':a=rng.integers(0,2,size=(2,8,8))*np.pi
                if name=='random_angles':a=rng.uniform(-np.pi,np.pi,size=(2,8,8))
                for charge in [0,1]:
                    result['patterns'].append({'pattern':name,'rep':rep,'theta':t,'charge':charge,
                        **C.eigen(a,charge)})
                print('pattern',name,rep,t,result['patterns'][-2]['lambda_min'],result['patterns'][-1]['lambda_min'],flush=True)
    # Independent dense spectral check of the smallest collar.
    C=Collar(8,1);A=C.assemble(uniform(8,np.pi),0).toarray()
    ev=np.linalg.eigvalsh(A)
    result['dense_check']={'dimension':len(ev),'lambda_min':float(ev[0]),
                          'expected_minus_4_sqrt5':float(-4*np.sqrt(5)),
                          'error':float(abs(ev[0]+4*np.sqrt(5)))}
    # Exact rational 3-variable reduction: norm=n^2+m^2+2t^2,
    # quadratic=-8n^2+8m^2-8(n+m)t, for transverse checkerboard.
    B=np.array([[(-1.)**(x[1]+x[2])*(1 if x[0]==-1 else (1/16 if d==0 else 1/4))
                 for x,d in C.bonds]],complex)[0]
    rq=float((B.conj()@A@B).real/(B.conj()@B).real)
    result['rational_witness']={'n':1,'m':'1/16','t':'1/4','quotient':rq,
                               'exact_quotient':'-2584/289','error':abs(rq+2584/289)}
    assert result['dense_check']['error']<1e-10 and result['rational_witness']['error']<1e-10
    rows=result['normal_only']+result['uniform_grid']+result['width_convergence']+result['patterns']
    result['min_observed']=min(rows,key=lambda r:r['lambda_min'])
    result['max_residual']=max(r['residual'] for r in rows)
    result['seconds']=time.time()-start
    result['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    (OUT/'search.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['min_observed','max_residual','seconds','peak_rss_kib']},indent=2))
if __name__=='__main__':main()
