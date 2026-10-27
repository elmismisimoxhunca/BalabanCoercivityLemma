#!/usr/bin/env python3
"""Screen the exact L3 low-cancellation family at another q,R instance."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
import screen_long as s
import argparse
OUT=Path(__file__).resolve().parent
s.OUT=OUT

def make(c2,c3):
    c=s.original()
    for b in [s.axial(1,1),s.axial(1,-2),s.axial(2,1),s.axial(2,-2)]:c[b]=c2
    for b in [s.axial(1,2),s.axial(1,-3),s.axial(2,2),s.axial(2,-3)]:c[b]=c3
    return c

def variants():
    ans=[('original',s.original()),('candidate',make(-.25,-2.25)),
         ('control_c2_m0_5_c3_m1_75',make(-.5,-1.75)),
         ('c2_0_c3_m2_25',make(0,-2.25)),
         ('c2_m0_25_c3_m2',make(-.25,-2)),
         ('c2_m0_25_c3_m2_5',make(-.25,-2.5)),
         ('c2_m0_5_c3_m2_25',make(-.5,-2.25)),
         ('c2_m0_4_c3_m2',make(-.4,-2))]
    return ans

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,required=True);ap.add_argument('--R',type=int,required=True)
    a=ap.parse_args();s.run(a.q,a.R,variants(),f'L3_q{a.q}_R{a.R}',3)
