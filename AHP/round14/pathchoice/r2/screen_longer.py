#!/usr/bin/env python3
"""Length-three exterior-arm screen, reusing the round-1 full-drive code."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
import screen_long as s
OUT=Path(__file__).resolve().parent
s.OUT=OUT

def alternating(length):
    c={}
    for mu in [1,2]:
        for k in range(-length,length):
            # Original two segments +t, second segments -t, third +t, ...
            level=max(0,abs(k)-1) if k<0 else k
            c[s.axial(mu,k)]=1 if level%2==0 else -1
    return c

def variants():
    ans=[]
    def add(name,c): ans.append((name,c))
    add('original',s.original())
    c2=alternating(2); add('length2_alternating_control',c2)
    c3=alternating(3); add('length3_alternating',c3)
    new=[s.axial(1,2),s.axial(1,-3),s.axial(2,2),s.axial(2,-3)]
    for mask in range(16):
        c=dict(c2); signs=[]
        for i,b in enumerate(new):
            v=1 if mask>>i&1 else -1; c[b]=v; signs.append(v)
        add('third_signs_'+'_'.join('p' if v>0 else 'm' for v in signs),c)
    for value in [-3.,-2.,-1.,-.5,0.,.5,1.,2.,3.]:
        c=dict(c2)
        for b in new:c[b]=value
        add('third_all_'+str(value),c)
    for a,b in [(-2,-1),(-1,-2),(-1,1),(1,-1),(2,1),(1,2),(2,-1),(-1,2),
                (.5,-1),(-1,.5),(.5,1),(1,.5)]:
        c=dict(c2)
        for x in [s.axial(1,2),s.axial(1,-3)]:c[x]=a
        for x in [s.axial(2,2),s.axial(2,-3)]:c[x]=b
        add(f'third_mu_{a}_{b}',c)
    # Remove exact duplicates while retaining the first descriptive name.
    out=[];seen=set()
    for name,c in ans:
        key=tuple(sorted(c.items()))
        if key not in seen:seen.add(key);out.append((name,c))
    return out

if __name__=='__main__':
    s.run(2,20,variants(),'L3_extensions',3)
