#!/usr/bin/env python3
"""Debug one D4 character transform against direct flat solves."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
sys.path.insert(0,str(ROOT/'AHP/round14/assembly/r2'))
from right_star import geometry
import time
q,R,N=2,20,8
mp.mp.dps=30
boundary=q*(12*R+12);pls,bonds=geometry(boundary,'right');n=len(bonds)

def character_matrix(iy,iz):
 f=Family(q,R,mp.mpf(0),iy,iz,1).assemble();out,_=f.plaq('out',0)
 for i,row in enumerate(out.r):
  if i in f.em:
   for j,v in row.items():
    if j in f.em:f.aug.put(f.em[i],f.em[j],v)
 phis=[f.index(*b) for b in bonds];solver=Refine(f.aug);M=mp.matrix(n)
 for col,(j,phase) in enumerate(phis):
  rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase);x=solver.solve(rhs)
  for row,(i,ph) in enumerate(phis):M[row,col]+=ph*x[f.em[i]]
 old_phase={b:ph for b,(i,ph) in zip(bonds,phis)}
 return M,old_phase

def phase(c,b):
 x,d=b
 return mp.exp(2j*mp.pi*c[0]/N)**(x[1]//2)*mp.exp(2j*mp.pi*c[1]/N)**(x[2]//2)

def main():
 rep=(0,1);other=(0,7);M,old=character_matrix(*rep);D,_=character_matrix(*other)
 mapped=[]
 for (a,b,c),d in bonds:
  c=-c
  candidate=((a,b,c),d)
  if candidate not in bonds:
   for dy in [0,2,-2]:
    for dz in [0,2,-2]:
     trial=((a,b+dy,c+dz),d)
     if trial in bonds:
      candidate=trial;break
    if candidate in bonds:break
  mapped.append(candidate)
 P=mp.matrix(n)
 for i in range(n):
  for j in range(n):
   z=conj(M[i,j]);rr=phase(other,mapped[i])/old[bonds[i]];cr=conj(phase(other,mapped[j]))/old[bonds[j]]
   P[bonds.index(mapped[i]),bonds.index(mapped[j])]+=rr*cr*z
 print('max direct-predicted',mp.mnorm(D-P,1),'direct',mp.mnorm(D,1),'pred',mp.mnorm(P,1))
 print('bonds',bonds);print('mapped',mapped)
 print('M support',[(i,j) for i in range(n) for j in range(n) if M[i,j]])
 print('D support',[(i,j) for i in range(n) for j in range(n) if D[i,j]])
 print('P support',[(i,j) for i in range(n) for j in range(n) if P[i,j]])
 print('M00',M[0,0],'M01',M[0,1],'D00',D[0,0],'D01',D[0,1])
 for i in range(n):
  print('ratios row',i,[(j,mp.nstr(D[i,j]/P[i,j],5) if P[i,j] else 'na') for j in range(n)])
 for i in range(n):
  for j in range(n):
   if abs(D[i,j]-P[i,j])>mp.mpf('1e-15'):
    print('entry',i,j,'direct',D[i,j],'pred',P[i,j],'ratio',D[i,j]/P[i,j] if P[i,j] else 'na');raise SystemExit
if __name__=='__main__':main()
