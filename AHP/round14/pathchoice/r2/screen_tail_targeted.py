#!/usr/bin/env python3
"""Targeted exact/simple coefficients around the low-cancellation L3 regime."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
import screen_long as s
OUT=Path(__file__).resolve().parent
s.OUT=OUT

def variants():
    ans=[]
    for c2 in [-1.,-.85,-.75,-2/3,-.6,-.5,-.4,-1/3,-.25,0.]:
        for c3 in [-3.,-2.5,-2.25,-2.,-1.9,-1.75,-1.6,-1.5]:
            c=s.original()
            for b in [s.axial(1,1),s.axial(1,-2),s.axial(2,1),s.axial(2,-2)]:c[b]=c2
            for b in [s.axial(1,2),s.axial(1,-3),s.axial(2,2),s.axial(2,-3)]:c[b]=c3
            ans.append((f'c2_{c2:.12g}_c3_{c3:.12g}',c))
    return ans

if __name__=='__main__':s.run(2,20,variants(),'L3_targeted',3)
