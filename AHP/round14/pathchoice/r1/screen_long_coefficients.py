#!/usr/bin/env python3
"""Reproduce the 202 second-segment variants in screen_long_coeffs_q2.log."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import screen_long as s
orig=s.original();ext=[s.axial(1,1),s.axial(1,-2),s.axial(2,1),s.axial(2,-2)]
variants=[];seen=set()
def add(name,cs):
    c=dict(orig);c.update(dict(zip(ext,cs)));key=tuple(cs)
    if key not in seen:seen.add(key);variants.append((name,c))
vals=[-3.,-2.5,-2.,-1.75,-1.5,-1.25,-1.,-.75,-.5,-.25,0.,.25,.5,1.,1.5,2.]
for c in vals:add('all_'+str(c),(c,c,c,c))
grid=[-2.,-1.5,-1.,-.5,0.,.5,1.]
for c in grid:
    for d in grid:
        add('mu_'+str(c)+'_'+str(d),(c,c,d,d))
        add('sgn_'+str(c)+'_'+str(d),(c,d,c,d))
        add('outer_'+str(c)+'_'+str(d),(c,d,d,c))
for i in range(4):
    for c in vals:
        cs=[0.,0.,0.,0.];cs[i]=c;add('single_'+str(i)+'_'+str(c),tuple(cs))
assert len(variants)==202
if __name__=='__main__':s.run(2,20,variants,'second_coeffs',2)
