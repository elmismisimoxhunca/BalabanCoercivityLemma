#!/usr/bin/env python3
"""Inspect the flat augmented/gauge rows near Omega_1. Numerical evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family, mp
import resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
mp.mp.dps=50
f=Family(1,20,mp.mpf(0),1,0,1).assemble()
print('s,hi,n,Hn',f.s,f.hi,f.n,f.H.n)
for x in range(f.s-2,f.s+7):
    inds=[f.em[f.bi[((x,y,z),d)]] for y,z in [(0,0),(1,0),(0,1),(1,1)] for d in range(3)
          if ((x,y,z),d) in f.bi and f.bi[((x,y,z),d)] in f.em]
    print('x',x,'Fstar_col_l1',[(i,max(sum(abs(f.F.r[k].get(i,0)) for k in range(f.H.n)),mp.mpf(0))) for i in inds],
          'V_row_l1',[(i,max(sum(abs(f.V.r[i].get(j,0)) for j in range(f.G.n)),mp.mpf(0))) for i in inds])
