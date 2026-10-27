#!/usr/bin/env python3
"""Reproduce the 112 weighted-arm variants used in screen_coefficients_q2.log."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import screen_signed
vals=[-2.,-1.,-.5,-.25,0.,.25,.5,.75,1.,1.25,1.5,2.]
small=[-1.,-.5,0.,.5,1.]
variants=[]
def add(v):
    v=tuple(float(x) for x in v)
    if v not in variants:variants.append(v)
for c in vals:
    add((1,c,1,c));add((1,1,c,c));add((1,c,c,c));add((1,c,1,1));add((1,c,c,1))
for c in small:
    for d in small:
        add((1,c,1,d));add((1,c,d,d));add((1,1,c,d));add((1,c,d,1))
assert len(variants)==112
if __name__=='__main__':screen_signed.run(2,20,variants,False,'coefficients')
