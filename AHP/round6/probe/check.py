#!/usr/bin/env python3
"""Independent transcription comparison at R=2 (NOT a requested-radius result).
All original helper imports are read-only. Operator anchors: SOURCES.md.
"""
import sys,os
sys.dont_write_bytecode=True
sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parents[2]/'round5/guarded/ivt-r2/numerics'))
import sys
sys.dont_write_bytecode = True
from probe import *
from crossing import SingleSlab,local_jac
from assembly import assemble,Raw
from scipy.linalg import solve
mp.mp.dps=60
eps=mp.mpf('0.0015625');f=Family(1,2,eps).assemble()
lat=SingleSlab(2);raw,W,fixed,hj,checks=assemble(lat,float(eps))
B=W.T@lat.delta_matrix(lat.config(0,float(eps)),'in')@W+fixed
# Original full color uses e1 neutral, (e2,e3) charged with z=e2+i*e3.
# Original x ranges 0..39 and new family agrees.
idx1=np.arange(1,B.shape[0],3);idx2=idx1+1
Bc=B[np.ix_(idx1,idx1)]+1j*B[np.ix_(idx2,idx1)]
A=f.aug.scipy().toarray();n=f.n;ours=A[:n,:n]-A[:n,n:]@solve(A[n:,n:],A[n:,:n],assume_a='her')
Q=raw.jac(0)[1::3,1::3]+1j*raw.jac(0)[2::3,1::3]
qt=f.Q.scipy().toarray()[len(f.b0):]
G=f.G.scipy().toarray();F=f.F.scipy().toarray();H=f.H.scipy().toarray()
wf=np.eye(len(f.bonds))[:,f.e]-G@solve(H,F,assume_a='her')
wc=W[np.ix_(np.arange(1,lat.dim,3),idx1)]+1j*W[np.ix_(np.arange(2,lat.dim,3),idx1)]
rng=np.random.default_rng(12);v=rng.normal(size=n)+1j*rng.normal(size=n);v/=np.linalg.norm(v)
w=wf@v
neutral=Family(1,2,eps,charge=0).assemble();h,hres=neutral.hj()
d,terms=f.correction(list(map(mp.mpc,w)),h)
origw=np.zeros(lat.dim);origw[1::3]=w.real;origw[2::3]=w.imag
from jet2 import raw_jet
dold=2*hj@raw_jet(raw,origw)[2]
report=dict(B_error=float(np.max(np.abs(ours-Bc))),Q_error=float(np.max(np.abs(qt-Q))),
 W_error=float(np.max(np.abs(wf-wc))),HtJ_error=float(np.max(np.abs(np.array([complex(x) for x in h])-hj[::3]))),
 D_new=fmt(d),D_old=dold,D_error=float(abs(d-dold)),HtJ_mp_residual=fmt(hres))
print(json.dumps(report,indent=2));(OUT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
assert report['B_error']<1e-10 and report['Q_error']<1e-10 and report['W_error']<1e-10
assert report['HtJ_error']<1e-10 and report['D_error']<1e-10
