#!/usr/bin/env python3
"""Search q=4 for common-sign paths with cosine-positive outer arms."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
import screen_long as s
from screen_tail_instance import make
OUT=Path(__file__).resolve().parent
s.OUT=OUT

def variants():
    ans=[]
    for c2 in [-1.,-.75,-.5,-.25,0.,.25]:
        for c3 in [-2.5,-2.25,-2.,-1.75,-1.5,-1.25,-1.,-.75,-.5]:
            ans.append((f'c2_{c2:.12g}_c3_{c3:.12g}',make(c2,c3)))
    return ans

if __name__=='__main__':s.run(4,18,variants(),'L3_q4_sweep',3)
