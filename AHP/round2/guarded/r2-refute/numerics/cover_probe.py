#!/usr/bin/env python3
"""Numerical test on the FULL (8,8,8) torus; not a proof or a class witness.

Operators and exact frozen Lean references: assembly.py header. In particular:
Ginv = W* Delta_all W + T*T + Mass (R2Algebra.lean:145;
ZXR2Ops3.lean:134; D1Lit.lean:59), correction diagonal
2 <H C2(v),J> (R2Algebra.lean:222), polarized second jet
(R2Algebra.lean:212), and TorusOK (ZStatementP428.lean:286).

We numerically compare periodic lifts of W and H*J, then check the spectrum
of the ENTIRE enlarged carrier (3648 real coordinates). The periodic-sector
candidate is recomputed from real raw-jet finite differences, not imported
from a numeric snapshot. Translation invariance has NOT been proved in Lean.
All files are written beside this script; 3500 MiB address-space cap inherited.
"""
import sys
sys.dont_write_bytecode = True
import json
import time
import resource
import numpy as np
from scipy.linalg import eigh
from assembly import Slab, assemble, OUT

start=time.time()
eps=0.16
theta=0.5771896115174016
small=Slab()
raws,Ws,Fs,hjs,cs=assemble(small,eps)
Ms=Ws.T@small.delta_matrix(small.config(theta,eps),'all')@Ws+Fs
Ms=(Ms+Ms.T)/2
ns=len(small.eidx)
# Matrix-free correction, same polarized raw formula as round 1.
def action(x,h=0.001):
    s=np.linalg.norm(x)
    if s<1e-40:return np.zeros(ns)
    wx=Ws@(x/s); out=np.zeros(ns)
    for i in range(0,ns,48):
        j=min(i+48,ns);b=Ws[:,i:j].T
        f=lambda a: raws.eval(a)@hjs
        out[i:j]=(f(h*(wx+b))-f(h*(wx-b))-f(h*(-wx+b))+f(h*(-wx-b)))/(4*h*h)
    return s*out
from scipy.linalg import cho_factor,cho_solve
from scipy.sparse.linalg import LinearOperator,lobpcg
es,Vs=eigh(Ms,subset_by_index=[0,2])
cf=cho_factor(Ms+0.01*np.eye(ns))
op=LinearOperator((ns,ns),matvec=lambda x:Ms@np.asarray(x).reshape(ns)-action(np.asarray(x).reshape(ns)),dtype=float)
pre=LinearOperator((ns,ns),matvec=lambda x:cho_solve(cf,x),dtype=float)
ev,V,res=lobpcg(op,Vs[:,:1],M=pre,largest=False,tol=2e-9,maxiter=40,retResidualNormsHistory=True)
v=V[:,0];dv=action(v)
smallcheck=dict(eigenvalue=float(ev[0]),residual=float(np.linalg.norm(Ms@v-dv-ev[0]*v)),carrier_min=float(es[0]))
print('recomputed periodic-sector candidate',smallcheck,flush=True)

large=Slab((8,8,8))
rawl,Wl,Fl,hjl,cl=assemble(large,eps)
print('enlarged assembly',cl,flush=True)
# Unit-normalized lift: each base-cell coordinate occurs four times, scale 1/2.
semap={int(j):i for i,j in enumerate(small.eidx)}
colmap=[]
for ix in large.eidx:
    b=large.bonds[int(ix)//3];x,mu=b
    bs=((x[0],x[1]%4,x[2]%4),mu)
    colmap.append(semap[3*small.bond_index[bs]+int(ix)%3])
colmap=np.array(colmap)
rowmap=[]
for b in large.bonds:
    x,mu=b; bs=((x[0],x[1]%4,x[2]%4),mu)
    rowmap.extend([3*small.bond_index[bs]+c for c in range(3)])
rowmap=np.array(rowmap)
vl=v[colmap]/2
wsmall=Ws@v
wl=Wl@vl
werror=float(np.max(np.abs(wl-wsmall[rowmap]/2)))
# The source is repeated without normalization, so H*J repeats without 1/2.
bmap={b:i for i,b in enumerate(small.b1)}
topmap=[]
for x,mu in large.b1:
    bs=((x[0],x[1]%4,x[2]%4),mu)
    topmap.extend([3*bmap[bs]+c for c in range(3)])
herror=float(np.max(np.abs(hjl-hjs[np.array(topmap)])))
print('lift checks',werror,herror,flush=True)
def large_action(x,h):
    n=len(large.eidx);s=np.linalg.norm(x)
    if s<1e-40:return np.zeros(n)
    wx=Wl@(x/s);out=np.zeros(n)
    for i in range(0,n,48):
        j=min(i+48,n);b=Wl[:,i:j].T
        f=lambda a: rawl.eval(a)@hjl
        out[i:j]=(f(h*(wx+b))-f(h*(wx-b))-f(h*(-wx+b))+f(h*(-wx-b)))/(4*h*h)
    return s*out
# Evaluate the enlarged raw jet in EVERY carrier coordinate independently of
# the proposed lift relation. Agreement is a diagnostic, not a lift theorem.
direct_actions={h:large_action(vl,h) for h in [0.003,0.001,0.0003]}
direct_lift_errors={str(h):float(np.linalg.norm(d-action(v,h/2)[colmap]/2))
                    for h,d in direct_actions.items()}
print('direct full correction versus periodic lift',direct_lift_errors,flush=True)
rows=[]
for t in [theta-1e-7,theta,theta+1e-7]:
    M=Wl.T@large.delta_matrix(large.config(t,eps),'all')@Wl+Fl
    M=(M+M.T)/2
    e=eigh(M,eigvals_only=True)
    ds=action(v)
    predicted_d=ds[colmap]/2
    # Full eigenvalue guard diagnostics; this does NOT infer units from a sector.
    row=dict(theta=t,carrier_min=float(e[0]),carrier_min_abs=float(np.min(np.abs(e))),
             carrier_negative_count=int(np.sum(e<0)),carrier_next_smallest_abs=np.sort(np.abs(e))[:12].tolist(),
             periodic_corrected_residual=float(np.linalg.norm(M@vl-predicted_d)),
             periodic_corrected_rayleigh=float(vl@(M@vl-predicted_d)),
             direct_correction=[dict(h=h,residual=float(np.linalg.norm(M@vl-d)),
                 rayleigh=float(vl@(M@vl-d))) for h,d in direct_actions.items()])
    rows.append(row);print(row,flush=True)
forms=[]
for h in [0.003,0.001,0.0003]:
    forms.append(dict(h=h,large=float(2*hjl@rawl.c2(wl,h)),small=float(2*hjs@raws.c2(wsmall,h/2))))
# Exhaust all unit-side conditions arithmetically; formal TorusOK check is separate.
unit=[n//2 for n in large.sides]
payload=dict(warning='numerics only: torus condition repaired, NO admissibility/coverage/class/cofinal certificate',
    ell=2,k=1,M=2,eps=eps,sides=large.sides,unit_sides=unit,
    torus_arithmetic=all(n%2==0 and 2<n for n in unit),carrier_dimension=len(large.eidx),
    small=smallcheck,checks=cl,W_lift_error=werror,HtJ_repeat_error=herror,
    quadratic_lift_checks=forms,direct_D_lift_errors=direct_lift_errors,
    rows=rows,seconds=time.time()-start,
    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(OUT/'cover_results.json').write_text(json.dumps(payload,indent=2))
