#!/usr/bin/env python3
"""Extract the full two-sublattice flat-collar matrix recurrence. Evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family, mp
import argparse,json,resource
import numpy as np
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent
CELLS=[(0,0),(1,0),(0,1),(1,1)]

def run(q,R,iy,iz,x,dps):
    mp.mp.dps=dps
    f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
    def var(x,y,z,d): return f.em.get(f.bi[((x,y,z),d)])
    def entry(x,a,d,y,b,e):
        ya,za=CELLS[a]; yb,zb=CELLS[b]
        i,j=var(x,ya,za,d),var(y,yb,zb,e)
        if i is None or j is None:return mp.mpc(0)
        return f.K.r[i].get(j,0)
    # Index is 4*(direction)+cell. Longitudinal directions 0 are eliminated below.
    def idx(a,d):return 3*a+d
    blocks={str(dx):[[entry(x,a,d,x+dx,b,e) for b in range(4) for e in range(3)]
        for a in range(4) for d in range(3)] for dx in range(-2,3)}
    # Reorder rows/columns to longitudinal four, then the eight transverse entries.
    order=[idx(a,d) for d in range(3) for a in range(4)]
    def mat(dx):
        raw=blocks[str(dx)]
        return mp.matrix([[raw[i][j] for j in order] for i in order])
    kp,km,k0=mat(1),mat(-1),mat(0)
    far={dx:max((abs(v) for row in blocks[str(dx)] for v in row),default=0) for dx in range(-2,3)}
    result={'q':q,'R':R,'character':[iy,iz],'x':x,'s':f.s,'hi':f.hi,
      'cells':CELLS,'blocks':blocks,'nonzero_by_dx':{str(k):str(v) for k,v in far.items()},
      'hermitian_jump_errors':[mp.mnorm(kp-km.H,1),mp.mnorm(k0-k0.H,1)]}
    a00,a01,a10,a11=kp[:4,:4],kp[:4,4:],kp[4:,:4],kp[4:,4:]
    b00,b01,b10,b11=k0[:4,:4],k0[:4,4:],k0[4:,:4],k0[4:,4:]
    c00,c01,c10,c11=km[:4,:4],km[:4,4:],km[4:,:4],km[4:,4:]
    result['elimination_norms']={'A00':mp.mnorm(a00,1),'C00':mp.mnorm(c00,1),
      'A10':mp.mnorm(a10,1),'C01':mp.mnorm(c01,1),'B00_inverse_residual':mp.mnorm(b00*b00**-1-mp.eye(4),1)}
    npkp=np.array([[complex(kp[i,j]) for j in range(12)] for i in range(12)])
    result['Kplus_determinant']=complex(np.linalg.det(npkp))
    if abs(result['Kplus_determinant'])>mp.power(10,-dps+5):
      result['Kplus_inverse_residual']=mp.mnorm(kp*kp**-1-mp.eye(12),1)
      T=mp.zeros(24)
      T[:12,:12]=-kp**-1*k0;T[:12,12:]=-kp**-1*km;T[12:,:12]=mp.eye(12)
      ev=mp.eig(T)[0]
      result['transfer_eigenvalues']=list(ev)
      result['transfer_determinant']=mp.det(T)
      result['transfer_eigenvalue_moduli']=sorted([abs(z) for z in ev])
    else:
      assert mp.mnorm(a00,1)<mp.power(10,-dps+5) and mp.mnorm(c00,1)<mp.power(10,-dps+5)
      assert mp.mnorm(a10,1)<mp.power(10,-dps+5) and mp.mnorm(c01,1)<mp.power(10,-dps+5)
      ar=a11-b10*b00**-1*a01
      br=b11-b10*b00**-1*b01-c10*b00**-1*a01
      cr=c11-c10*b00**-1*b01
      result['reduced_shape']=[ar.rows,ar.cols]
      result['reduced_hermitian_jump_errors']=[mp.mnorm(ar-cr.H,1),mp.mnorm(br-br.H,1)]
      result['reduced_determinants']={'A':mp.det(ar),'C':mp.det(cr)}
      T=mp.zeros(16)
      T[:8,:8]=-ar**-1*br;T[:8,8:]=-ar**-1*cr;T[8:,:8]=mp.eye(8)
      ev=mp.eig(T)[0]
      result['transfer_eigenvalues']=list(ev)
      result['transfer_determinant']=mp.det(T)
      result['transfer_eigenvalue_moduli']=sorted([abs(z) for z in ev])
      result['reduced_blocks']={'A':[[ar[i,j] for j in range(8)] for i in range(8)],
        'B':[[br[i,j] for j in range(8)] for i in range(8)],
        'C':[[cr[i,j] for j in range(8)] for i in range(8)]}
    target=OUT/f'full_q{q}_R{R}_c{iy}_{iz}_x{x}.json'
    target.write_text(json.dumps(result,default=lambda z:str(z),indent=2)+'\n')
    print('SUMMARY',json.dumps({k:v for k,v in result.items() if k not in ['blocks','reduced_blocks']},default=lambda z:str(z),indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=20)
    p.add_argument('--iy',type=int,default=0);p.add_argument('--iz',type=int,default=0)
    p.add_argument('--x',type=int,default=220);p.add_argument('--dps',type=int,default=50)
    a=p.parse_args();run(a.q,a.R,a.iy,a.iz,a.x,a.dps)
