#!/usr/bin/env python3
"""Matrix-free probe of the ACTUAL Delta2 quadratic-form Hessian.
All operator references, small geometry and caveats: probe_assembled.py header.
R2Algebra.lean:222 gives Delta2 = Hessian_x <H^T J, Qraw(W x)> at 0.
Here Qraw includes ell^-j and its level-0 Hessian is zero.
The matrix-free action uses polarized finite differences, NOT Delta(eps)-Delta(0).
No exact singularity, full inverse existence, class or headline is certified.
"""
import sys
sys.dont_write_bytecode=True
import json
import time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh, cho_factor, cho_solve
from scipy.sparse.linalg import LinearOperator, lobpcg
from probe_assembled import Slab,assemble,OUT

start=time.time();eps=0.16
lat=Slab();raw,W,fixed,hj,checks=assemble(lat,eps)
n=W.shape[1]
root0=0.5771901710052161
counts={'actions':0}

def carrier(t):
    D=lat.delta_matrix(lat.config(t,eps),'all')
    M=W.T@D@W+fixed
    return (M+M.T)/2

def action(x,h):
    x=np.asarray(x).reshape(n);s=np.linalg.norm(x)
    if s<1e-40:return np.zeros(n)
    wx=W@(x/s);out=np.zeros(n)
    for i in range(0,n,48):
        j=min(i+48,n);b=W[:,i:j].T
        f=lambda a: raw.eval(a)@hj
        out[i:j]=(f(h*(wx+b))-f(h*(wx-b))-f(h*(-wx+b))+f(h*(-wx-b)))/(4*h*h)
    counts['actions']+=1
    return s*out

rows=[]
# Track the lowest eigenpair of the full 960-dimensional corrected operator.
# No compression: every matvec includes all E coordinates.
for h in [0.003,0.001,0.0003]:
    def calc(t):
        M=carrier(t);e,V=eigh(M,subset_by_index=[0,2])
        cache={}
        def act(x):
            return M@np.asarray(x).reshape(n)-action(x,h)
        op=LinearOperator((n,n),matvec=act,dtype=float)
        fact=cho_factor(M+0.01*np.eye(n))
        pre=LinearOperator((n,n),matvec=lambda x:cho_solve(fact,x),dtype=float)
        ev,Vv,res=lobpcg(op,V[:,:1],M=pre,largest=False,tol=2e-9,maxiter=35,retResidualNormsHistory=True)
        v=Vv[:,0];dv=action(v,h)
        rr=float(np.linalg.norm(M@v-dv-ev[0]*v))
        row=dict(h=h,theta=t,corrected_lowest=float(ev[0]),residual=rr,
             carrier_lowest_three=e.tolist(),carrier_min_abs=float(np.min(np.abs(e))),
             v_D_v=float(v@dv),D_v_norm=float(np.linalg.norm(dv)),iterations=len(res)-2)
        rows.append(row);print(row,flush=True)
        if h==0.001 and abs(float(ev[0]))<1e-8:
            np.savez(OUT/'candidate.npz',eps=eps,theta=t,v=v,eidx=lat.eidx,
                     carrier_action=M@v,correction_action=dv)
        return ev[0]
    f0=calc(root0)
    f1=calc(root0+2e-6)
    # A secant location is only a diagnostic, not an exact root certificate.
    t=root0-f0*2e-6/(f1-f0)
    calc(float(t))
    if h==0.001:
        calc(float(t-1e-7))
        calc(float(t+1e-7))
# Independent step-size and Hessian symmetry diagnostics, not error bounds.
q_error=float(np.max(np.abs(raw.jac(2e-5)-raw.jac(1e-5))))
rng=np.random.default_rng(197)
x=rng.normal(size=n);x/=np.linalg.norm(x)
y=rng.normal(size=n);y/=np.linalg.norm(y)
dx=action(x,0.001);dy=action(y,0.001)
symmetry_error=float(abs(x@dy-y@dx))
form_error=float(abs(x@dx-2*hj@raw.c2(W@x,0.001)))
payload=dict(warning='numerical full-space root separation only; NOT a Lean/class/cofinal certificate',
   eps=eps,checks=checks,rows=rows,Q_step_difference=q_error,
   Hessian_symmetry_error=symmetry_error,Hessian_vs_directional_form_error=form_error,
   actions=counts['actions'],seconds=time.time()-start,
   peak_rss_kib=__import__('resource').getrusage(__import__('resource').RUSAGE_SELF).ru_maxrss)
(OUT/'separation_results.json').write_text(json.dumps(payload,indent=2))
