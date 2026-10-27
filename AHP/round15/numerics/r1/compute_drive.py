#!/usr/bin/env python3
"""Compute the right-star nine-bond Schur drive at one reference radius.
This is non-interval numerical evidence, not a Lean certificate. All writes stay
beside this script. The flat augmented operator is assembled before restriction.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
sys.path.insert(0,str(ROOT/'AHP/round14/assembly/r2'))
from right_star import geometry,perturbation
import argparse,json,time,resource,gc
import numpy as np
from scipy.sparse.linalg import splu
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

class BlockRefine:
    """Mixed-precision block iterative refinement; final residuals use mp data."""
    def __init__(self,A):
        self.A=A;self.AS=A.scipy();self.lu=splu(self.AS)
    def solve_columns(self,rhs):
        n=len(rhs);m=len(rhs[0]);B=np.array([[complex(v) for v in row] for row in rhs],dtype=np.complex128)
        X=[[mp.mpc(0) for _ in range(m)] for _ in range(n)]
        R=B.copy();bn=max(abs(B).max(),1.0);tol=mp.power(10,-mp.mp.dps+8);history=[]
        for k in range(2+mp.mp.dps//10):
            rn=float(abs(R).max());history.append(rn/bn)
            if rn/bn<tol:break
            D=self.lu.solve(R/rn)
            for i in range(n):
                for j in range(m):X[i][j]+=rn*mp.mpc(float(D[i,j].real),float(D[i,j].imag))
            if k == 0:
                Xn=np.array([[complex(v) for v in row] for row in X],dtype=np.complex128)
                R=B-self.AS@Xn
            else:
                # Double residuals stall near epsilon; subsequent residuals are
                # evaluated with the original sparse mpmath coefficients.
                R=np.empty_like(B)
                for j in range(m):
                    ax=self.A.apply([X[i][j] for i in range(n)])
                    for i in range(n):R[i,j]=complex(B[i,j]-ax[i])
        else:
            raise ArithmeticError('block refinement failed: '+str(history))
        return [[X[i][j] for j in range(m)] for i in range(n)],history

def run(q,R,dps):
    mp.mp.dps=dps;start=time.time();nchar=(4*q)**2;boundary=q*(12*R+12)
    pls,bonds=geometry(boundary,'right');n=len(bonds);C=mp.matrix(n);residual=mp.mpf(0)
    for iy in range(4*q):
      for iz in range(4*q):
        f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
        out,_=f.plaq('out',0)
        for i,row in enumerate(out.r):
          if i in f.em:
            for j,v in row.items():
              if j in f.em:f.aug.put(f.em[i],f.em[j],v)
        phis=[f.index(*b) for b in bonds];solver=BlockRefine(f.aug)
        rhs=[[0]*n for _ in range(f.aug.n)]
        for col,(j,phase) in enumerate(phis):rhs[f.em[j]][col]=conj(phase)
        xs,history=solver.solve_columns(rhs)
        for col,(j,phase) in enumerate(phis):
          x=[xs[i][col] for i in range(f.aug.n)];one=[rhs[i][col] for i in range(f.aug.n)]
          residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),one)))
          for row,(i,ph) in enumerate(phis):C[row,col]+=ph*x[f.em[i]]/nchar
        print('SECTOR',iy,iz,'seconds',time.time()-start,'refine',history[-1],flush=True)
        del solver,xs;gc.collect()
    asym=mp.mnorm(C-C.H,1);C=(C+C.H)/2;S=C**-1
    base=perturbation(mp.mpf(0),1,pls,bonds,'right')
    def A(t):return S+perturbation(t,1,pls,bonds,'right')-base
    root=mp.findroot(lambda t:mp.eighe(A(t),eigvals_only=True)[0],
      (mp.mpf('1.19'),mp.mpf('1.22')),tol=mp.power(10,-dps+12),verify=True)
    vals,V=mp.eighe(A(root));v=V[:,0]
    drive=-(perturbation(root,1,pls,bonds,'right')-base)*v
    result={'q':q,'R':R,'dps':dps,'root':root,'charged_low':list(vals[:4]),
      'C':[[C[i,j] for j in range(n)] for i in range(n)],
      'eigenvector':list(v),'z':list(drive),
      'flat_resolvent_absolute_residual':residual,
      'compressed_resolvent_hermitian_error':asym,'boundary_null_residual':mp.mnorm(A(root)*v,1),
      'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      'qualification':'Non-interval numerical evidence only; unit nine-bond Schur vector, not full-carrier normalization.'}
    target=OUT/f'drive_right_q{q}_R{R}_p{dps}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('SUMMARY',json.dumps(jsonable({k:v for k,v in result.items() if k not in ['C','eigenvector','z']}),indent=2),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,required=True);ap.add_argument('--R',type=int,required=True);ap.add_argument('--dps',type=int,default=40)
    a=ap.parse_args();run(a.q,a.R,a.dps)
