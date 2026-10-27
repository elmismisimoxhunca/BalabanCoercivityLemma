#!/usr/bin/env python3
"""Fine symmetric second/third segment coefficient sweep on the L3 cache."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
import screen_long as s
from screen_longer import alternating
OUT=Path(__file__).resolve().parent
s.OUT=OUT

def variants():
    vals=[-1.75,-1.5,-1.25,-1.1,-1.,-.95,-.9,-.85,-.8,-.75,-.7,-.6,-.5,-.4,-.25,0.,.25,.5]
    ans=[]
    for c2 in vals:
        for c3 in vals:
            c=s.original()
            for b in [s.axial(1,1),s.axial(1,-2),s.axial(2,1),s.axial(2,-2)]:c[b]=c2
            for b in [s.axial(1,2),s.axial(1,-3),s.axial(2,2),s.axial(2,-3)]:c[b]=c3
            ans.append((f'c2_{c2}_c3_{c3}',c))
    return ans

if __name__=='__main__':s.run(2,20,variants(),'L3_tail_sweep',3)
