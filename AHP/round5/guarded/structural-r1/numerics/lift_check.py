#!/usr/bin/env python3
"""Check all 16 carrier fibers and full-lattice raw derivatives at the tested cap.
Evidence only: no exact operator/Fourier theorem and no certified error bound.
"""
import sys
sys.dont_write_bytecode=True
import json, gc, itertools, time, resource
from pathlib import Path
import numpy as np
from assembly import Slab, Raw, expv, P, I
from observe import SingleSlab
import lift_probe
lift_probe.WideSlab=SingleSlab
OUT=Path(__file__).resolve().parent

class FullLift(SingleSlab):
    def __init__(self,R):
        self.R=R;self.p=2*R+4;self.q=10*R+12;self.lo=4;self.hi=12*R+12
        Slab.__init__(self,(12*R+16,8,8))
    def config(self,theta,eps):
        U={b:(P.u_theta(theta) if b in self._zb_set else I.copy()) for b in self.bonds}
        for y in range(0,8,2):
            for z in range(0,8,2):U[((self.p,y,z),1)]=expv(np.array([eps,0.,0.]))
        return U

start=time.time();base=json.loads((OUT/'observation_results.json').read_text());R=base['R'];eps=base['epsilon']
q=SingleSlab(R);uq=q.config(0,eps)
rows=[lift_probe.local_raw(q,uq,c) for c in q.b1]
sectors=[]
for iy,iz in itertools.product(range(4),repeat=2):
    row=lift_probe.sector(R,eps,base['rows'][-1]['theta'],iy,iz,rows)
    sectors.append(row);print(json.dumps(row),flush=True);gc.collect()
f=FullLift(R);uf=f.config(0,eps);rf=Raw(f,uf);rowix={b:i for i,b in enumerate(q.b1)}
rng=np.random.default_rng(138731);v=rng.normal(size=(q.nB,3))+1j*rng.normal(size=(q.nB,3))
v[[q.bond_index[b] for b in q.zb]]=0;v/=np.linalg.norm(v)
checks=[]
for iy,iz in [(0,0),(1,2)]:
    def phi(x):return np.exp(.5j*np.pi*(iy*(x[1]//2)+iz*(x[2]//2)))
    def fold(b):return ((b[0][0],b[0][1]%2,b[0][2]%2),b[1])
    lifted=np.array([phi(b[0])*v[q.bond_index[fold(b)]] for b in f.bonds]).ravel()
    pred=[]
    for used,J in rows:
        local=np.array([phi(b[0])*v[q.bond_index[fold(b)]] for b in used]).ravel()
        pred.append(J@local)
    fullpred=np.array([phi(b[0])*pred[rowix[fold(b)]] for b in f.b1]).ravel()
    h=1e-5;A=np.stack([h*lifted.real,-h*lifted.real,h*lifted.imag,-h*lifted.imag])
    ev=rf.eval(A);d=(ev[0]-ev[1]+1j*(ev[2]-ev[3]))/(2*h)
    row=dict(sector=[iy,iz],h=h,max_absolute_error=float(np.max(np.abs(d-fullpred))),
             expected_norm=float(np.linalg.norm(fullpred)),error_norm=float(np.linalg.norm(d-fullpred)))
    checks.append(row);print(json.dumps(row),flush=True)
    assert row['max_absolute_error']<1e-8
out=dict(status='numerical full-lift consistency only; no exact guard certificate',
         theta=base['rows'][-1]['theta'],epsilon=eps,physical_sides=list(f.sides),
         full_carrier_dimension=len(f.eidx),sectors=sectors,raw_checks=checks,
         minimum_carrier_abs_over_all_sectors=min(r['min_abs'] for r in sectors),
         total_sector_dimension=sum(r['dimension'] for r in sectors),seconds=time.time()-start,
         peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
assert out['total_sector_dimension']==out['full_carrier_dimension']
assert all(r['negative_count']==0 and r['min_abs']>1e-8 for r in sectors)
(OUT/'lift_checks.json').write_text(json.dumps(out,indent=2))
print('DONE',out['seconds'],out['peak_rss_kib'],flush=True)
