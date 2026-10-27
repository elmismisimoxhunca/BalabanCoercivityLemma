#!/usr/bin/env python3
"""General SU(2), source-normalized real 3-component collar Delta. Evidence only."""
import search as s  # same-directory module; installs thread/memory limits first
import itertools,json,time
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh
E=np.array([[[1j,0],[0,-1j]],[[0,1],[-1,0]],[[0,1j],[1j,0]]])
I=np.eye(2);I3=np.eye(3)
def matrix(q):return q[0]*I+np.einsum('a,aij->ij',q[1:],E)
def coords(U):return np.array([-np.trace(e@U).real/2 for e in E])
def rot(U):return np.array([[-np.trace(a@U@b@U.conj().T).real/2 for b in E] for a in E])
def cross(n):
    x,y,z=n
    return np.array([[0,-z,y],[z,0,-x],[-y,x,0]])
def local(U):
    hol=U[0]@U[1]@U[2].conj().T@U[3].conj().T
    c=np.trace(hol).real/2;n=coords(hol);N=cross(n)
    transforms=[I3,rot(U[0]),-rot(U[3]),-I3]
    H=np.zeros((12,12))
    for i in range(4):H[3*i:3*i+3,3*i:3*i+3]=c*I3
    for r,t in itertools.combinations(s.ORDER,2):
        H[3*r:3*r+3,3*t:3*t+3]=c*I3-N
        H[3*t:3*t+3,3*r:3*r+3]=c*I3+N
    T=np.zeros((12,12))
    for i in range(4):T[3*i:3*i+3,3*i:3*i+3]=transforms[i]
    return T.T@H@T

def assemble(C,quats):
    rr=[];cc=[];vv=[]
    for edges,ids in C.plaqs:
        U=[matrix(quats[d-1,x[1],x[2]]) if x[0]<0 and d else I for x,d in edges]
        H=local(U)
        for i in range(4):
            if ids[i]<0:continue
            for j in range(4):
                if ids[j]<0:continue
                for r in range(3):
                    for t in range(3):
                        v=H[3*i+r,3*j+t]
                        if v:rr.append(3*ids[i]+r);cc.append(3*ids[j]+t);vv.append(v)
    return coo_matrix((vv,(rr,cc)),shape=(3*len(C.bonds),)*2).tocsr()

def audit(rng):
    gap=0.;low=0.;high=0.
    for _ in range(40):
        quats=rng.normal(size=(4,4));quats/=np.linalg.norm(quats,axis=1)[:,None]
        U=[matrix(q) for q in quats];v=rng.normal(size=(4,3));X=np.einsum('ra,aij->rij',v,E)
        A=[X[0],U[0]@X[1]@U[0].conj().T,-U[3]@X[2]@U[3].conj().T,-X[3]]
        hol=U[0]@U[1]@U[2].conj().T@U[3].conj().T;curl=sum(A);herm=1j*curl
        comm=sum((1j*((1j*A[r])@(1j*A[t])-(1j*A[t])@(1j*A[r]))
                  for r,t in itertools.combinations(s.ORDER,2)))
        direct=(-np.trace(curl@curl).real+np.trace(herm@herm@((hol+hol.conj().T)/2-I)).real
                +np.trace(comm@((hol-hol.conj().T)/(2j))).real)/2
        H=local(U);vv=v.ravel();gap=max(gap,abs(vv@H@vv-direct))
        ev=np.linalg.eigvalsh(H);low=min(low,ev[0]);high=max(high,ev[-1])
    assert gap<1e-10 and low>=-4-1e-10 and high<=4+1e-10
    return {'plaquettes':40,'max_trace_formula_error':gap,'local_eigen_range':[low,high]}

def main():
    start=time.time();rng=np.random.default_rng(19265);C=s.Collar(8,4)
    result={'status':'numerical evidence only','audit':audit(rng),'samples':[]}
    for name in ['center_minus_one','orthogonal_axes_pi_half','haar','near_center']:
        for rep in range(5 if name in ['haar','near_center'] else 1):
            q=np.zeros((2,8,8,4));q[:,:,:,0]=-1
            if name=='orthogonal_axes_pi_half':q[:]=0;q[0,:,:,1]=1;q[1,:,:,2]=1
            if name=='haar':q=rng.normal(size=q.shape);q/=np.linalg.norm(q,axis=-1)[...,None]
            if name=='near_center':
                axis=rng.normal(size=(2,8,8,3));axis/=np.linalg.norm(axis,axis=-1)[...,None]
                angle=rng.uniform(.8*np.pi,1.2*np.pi,size=(2,8,8))
                q[:,:,:,0]=np.cos(angle);q[:,:,:,1:]=np.sin(angle)[...,None]*axis
            A=assemble(C,q);w,v=eigsh(A,k=1,which='SA',tol=1e-11,v0=rng.normal(size=A.shape[0]))
            row={'pattern':name,'rep':rep,'lambda_min':float(w[0]),'residual':float(np.linalg.norm(A@v[:,0]-w[0]*v[:,0]))}
            if name=='center_minus_one':
                expected=C.eigen(s.uniform(8,np.pi),0)['lambda_min'];row['abelian_gap']=abs(w[0]-expected)
                assert row['abelian_gap']<1e-9
            result['samples'].append(row);print(row,flush=True)
    result['seconds']=time.time()-start
    result['peak_rss_kib']=s.resource.getrusage(s.resource.RUSAGE_SELF).ru_maxrss
    (s.OUT/'nonabelian.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
