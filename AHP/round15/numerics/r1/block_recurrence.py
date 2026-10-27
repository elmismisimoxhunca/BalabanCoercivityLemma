#!/usr/bin/env python3
"""Exact sparse block recurrence for the frozen flat augmented right collar.
The output is the actual operator, not a fitted scalar ansatz. It includes all
bond and multiplier variables, interface rows, exterior-star entries and residuals.
"""
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
from area_sweep import mpc_string
import argparse,json,time,resource,gc
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def run(q,R,iy,iz,dps,drive_path):
    mp.mp.dps=dps;raw=json.loads(Path(drive_path).read_text());drive=[mpc_string(s) for s in raw['z']]
    boundary=q*(12*R+12);_,bonds=geometry(boundary,'right');f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
    out,_=f.plaq('out',0)
    for i,row in enumerate(out.r):
        if i in f.em:
            for j,v in row.items():
                if j in f.em:f.aug.put(f.em[i],f.em[j],v)
    phis=[f.index(*b) for b in bonds];solver=Refine(f.aug)
    Y=[mp.mpc(0)]*f.aug.n;rhs_total=[mp.mpc(0)]*f.aug.n;residual=mp.mpf(0);start=time.time()
    for col,(j,phase) in enumerate(phis):
        rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase);x=solver.solve(rhs)
        residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
        for k in range(f.aug.n):Y[k]+=drive[col]*x[k];rhs_total[k]+=drive[col]*rhs[k]
    descriptors=[]
    for i in range(f.n):
        x,d=f.bonds[f.e[i]];descriptors.append({'index':i,'kind':'bond','x':x[0],'y':x[1],'z':x[2],'direction':d})
    for i in range(f.n,f.aug.n):
        k=i-f.n;block=0 if k<f.H.n else 1;site_index=k if block==0 else k-f.H.n
        x=f.sites[site_index];descriptors.append({'index':i,'kind':'multiplier','x':x[0],'y':x[1],'z':x[2],'block':block})
    ay=f.aug.apply(Y);rows=[]
    for i in range(f.aug.n):
        x=descriptors[i]['x']
        if x<f.s-4 or x>=f.hi:continue
        ar=abs(ay[i]-rhs_total[i])
        term_scale=max((abs(v*Y[j]) for j,v in f.aug.r[i].items()),default=mp.mpf(0))
        scale=max(abs(ay[i]),abs(rhs_total[i]),term_scale)
        rows.append({'row':i,'descriptor':descriptors[i],'rhs':rhs_total[i],'AY':ay[i],
          'absolute_residual':ar,'relative_residual':ar/max(scale,mp.power(10,-dps+4))})
    blocks=[]
    for i in range(f.aug.n):
        rx=descriptors[i]['x']
        if rx<f.s-4 or rx>=f.hi:continue
        for j,v in f.aug.r[i].items():
            cx=descriptors[j]['x']
            blocks.append({'row_x':rx,'col_x':cx,'row':i,'col':j,'value':v})
    result={'q':q,'R':R,'character':[iy,iz],'dps':dps,'drive':str(drive_path),'root':raw['root'],
      's':f.s,'hi':f.hi,'augmented_dimension':f.aug.n,'descriptors':descriptors,
      'blocks':blocks,'rows':rows,'solution':Y,'flat_resolvent_absolute_residual':residual,
      'max_row_relative_residual':max((r['relative_residual'] for r in rows),default=mp.mpf(0)),
      'seconds':time.time()-start,
      'recurrence_convention':'For every listed row i, sum_{blocks with row=i} value * solution[col] = rhs. Blocks are grouped by row_x,col_x. This is the exact frozen flat+exterior-star operator, not a fitted recurrence.',
      'qualification':'Non-interval numerical operator and residuals. No scalar decoupling, interval proof, or Lean theorem is asserted.'}
    target=OUT/f'block_right_q{q}_R{R}_c{iy}_{iz}_p{dps}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('OUTPUT',target,'blocks',len(blocks),'rows',len(rows),'max rel',result['max_row_relative_residual'],'seconds',time.time()-start)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,required=True);ap.add_argument('--R',type=int,required=True)
    ap.add_argument('--iy',type=int,required=True);ap.add_argument('--iz',type=int,required=True);ap.add_argument('--dps',type=int,default=50);ap.add_argument('--drive',required=True)
    a=ap.parse_args();run(a.q,a.R,a.iy,a.iz,a.dps,a.drive)
