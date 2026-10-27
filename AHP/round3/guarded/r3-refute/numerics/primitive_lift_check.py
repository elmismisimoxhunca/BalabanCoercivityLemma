#!/usr/bin/env python3
"""Numerical full-lift raw-jet check, separate from fiber inverses.

Anchors under lean/src: R2Raw1.lean:36,43,68,74; R2RawX.lean:187;
ZLocJet.lean:35,39,89,100; ZXR2Sector.lean:97,109. Also see assembly.py.
Compares the raw directional derivative on the complete (40,8,8) lattice
against the local-path phase scatter used by lift_probe.py. Uses no quotient
identification for the full-lift derivative. This is not a Lean theorem or a
validated-error bound. No inverse or full corrected operator is assembled here.
"""
import sys
sys.dont_write_bytecode=True
import json,resource,time
from pathlib import Path
import numpy as np
from assembly import Slab,Raw,expv,P,I
from wide_probe import WideSlab
from lift_probe import local_raw
OUT=Path(__file__).resolve().parent

class FullLift(WideSlab):
    def __init__(self,R):
        self.R=R;self.p=2*R+4;self.q=10*R+12;self.lo=4;self.hi=12*R+12
        Slab.__init__(self,(12*R+16,8,8))
    def config(self,theta,eps):
        U={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        for y in range(0,8,2):
            for z in range(0,8,2):U[((self.p,y,z),1)]=expv(np.array([eps,0.,0.]))
        return U

start=time.time();R=2;eps=.04
q=WideSlab(R);uq=q.config(0,eps);uq[((q.p+1,1,0),2)]=I.copy()
f=FullLift(R);uf=f.config(0,eps);rf=Raw(f,uf)
rows=[local_raw(q,uq,c) for c in q.b1];rowix={b:i for i,b in enumerate(q.b1)}
rng=np.random.default_rng(138731);v=rng.normal(size=(q.nB,3))+1j*rng.normal(size=(q.nB,3))
v[[q.bond_index[b] for b in q.zb]]=0
v/=np.linalg.norm(v)
checks=[]
for iy,iz in [(0,0),(0,1),(1,2),(3,3)]:
    def phi(x):return np.exp(.5j*np.pi*(iy*(x[1]//2)+iz*(x[2]//2)))
    def fold(b):return ((b[0][0],b[0][1]%2,b[0][2]%2),b[1])
    lifted=np.array([phi(b[0])*v[q.bond_index[fold(b)]] for b in f.bonds]).ravel()
    pred=[]
    for used,J in rows:
        local=np.array([phi(b[0])*v[q.bond_index[fold(b)]] for b in used]).ravel()
        pred.append(J@local)
    fullpred=np.array([phi(b[0])*pred[rowix[fold(b)]] for b in f.b1]).ravel()
    vals=[]
    for h in [1e-4,1e-5]:
        A=np.stack([h*lifted.real,-h*lifted.real,h*lifted.imag,-h*lifted.imag])
        ev=rf.eval(A);d=(ev[0]-ev[1]+1j*(ev[2]-ev[3]))/(2*h)
        vals.append(dict(h=h,max_absolute_error=float(np.max(np.abs(d-fullpred))),
            expected_norm=float(np.linalg.norm(fullpred)),error_norm=float(np.linalg.norm(d-fullpred))))
    checks.append(dict(sector=[iy,iz],differences=vals))
    print(json.dumps(checks[-1]),flush=True)
    assert vals[-1]['max_absolute_error']<1e-8
payload=dict(status='numerical raw lift consistency only',full_fine_bonds=f.nB,
    full_raw_output_rows=len(f.b1),checks=checks,seconds=time.time()-start,
    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(OUT/'primitive_lift_results.json').write_text(json.dumps(payload,indent=2))
print('DONE',payload['seconds'],flush=True)
