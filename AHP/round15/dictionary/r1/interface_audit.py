#!/usr/bin/env python3
"""Locate the exact constant-collar and interface rows. Evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,mp
import argparse,json,resource,numpy as np
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent
CELLS=[(0,0),(1,0),(0,1),(1,1)]

def run(q,R,iy,iz,dps):
    mp.mp.dps=dps
    f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
    def var(x,y,z,d):return f.em.get(f.bi[((x,y,z),d)])
    def entry(x,a,d,y,b,e):
        ya,za=CELLS[a];yb,zb=CELLS[b];i,j=var(x,ya,za,d),var(y,yb,zb,e)
        return f.K.r[i].get(j,0) if i is not None and j is not None else 0
    order=[(a,d) for d in range(3) for a in range(4)]
    def mat(x,dx):return np.array([[complex(entry(x,a,d,x+dx,b,e)) for b,e in order] for a,d in order])
    deep=f.s+5
    records=[]
    for x in [f.s-2,f.s-1,f.s,f.s+1,f.s+2,deep,f.hi-2,f.hi-1]:
        if x<f.s or x>f.hi-1:continue
        records.append({'x':x,'K0_deep_difference':float(np.max(np.abs(mat(x,0)-mat(deep,0)))),
          'Kplus_deep_difference':float(np.max(np.abs(mat(x,1)-mat(deep,1)))),
          'Kminus_deep_difference':float(np.max(np.abs(mat(x,-1)-mat(deep,-1))))})
    # Auxiliary augmented-system interactions and exterior-plaquette changes by layer.
    aux=[];out,_=f.plaq('out',0)
    for x in range(f.s-2,f.hi):
        inds=[var(x,y,z,d) for y,z in CELLS for d in range(3)]
        inds=[i for i in inds if i is not None]
        vnorm=max((sum(abs(v) for v in f.V.r[i].values()) for i in inds),default=0)
        # F has auxiliary rows and physical columns.
        fnorm=max((sum(abs(v) for j,v in row.items() if j in inds) for row in f.F.r),default=0)
        onorm=max((sum(abs(v) for j,v in out.r[f.e[i]].items() if f.e[i] in f.em) for i in inds),default=0)
        aux.append({'x':x,'V_row_l1_max':str(vnorm),'F_column_l1_max':str(fnorm),'out_K_row_l1_max':str(onorm)})
    result={'q':q,'R':R,'character':[iy,iz],'s':f.s,'hi':f.hi,'deep_reference_x':deep,
      'constant_recurrence_claim':'K_- v_(x-1)+K_0 v_x+K_+ v_(x+1)=0 uses the same blocks for s+1<=x<=hi-2',
      'block_comparisons':records,'auxiliary_and_out_by_layer':aux,
      'qualification':'Non-interval numerical evidence only; interface rows are located, not yet identified in Lean.'}
    target=OUT/f'interface_q{q}_R{R}_c{iy}_{iz}.json'
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=20)
    p.add_argument('--iy',type=int,default=1);p.add_argument('--iz',type=int,default=0);p.add_argument('--dps',type=int,default=50)
    a=p.parse_args();run(a.q,a.R,a.iy,a.iz,a.dps)
