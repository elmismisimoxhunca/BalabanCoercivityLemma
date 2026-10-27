#!/usr/bin/env python3
"""Longitudinal mixed-area profile for the right-star crossing. Evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
sys.path.insert(0,str(ROOT/'AHP/round14/cancellation/r1'))
from structure_probe import geometry,perturbation
import argparse,json,time,resource,gc
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def run(q,R,dps,start_row,stop_row,direct_only,tag):
    mp.mp.dps=dps; start=time.time(); side='right'; nchar=(4*q)**2
    boundary=q*(12*R+12)
    pls,bonds=geometry(boundary,side); n=len(bonds); C=mp.matrix(n)
    rows=[]; residual=mp.mpf(0)
    for iy in range(4*q):
      for iz in range(4*q):
        f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
        out,_=f.plaq('out',0)
        for i,row in enumerate(out.r):
          if i in f.em:
            for j,v in row.items():
              if j in f.em: f.aug.put(f.em[i],f.em[j],v)
        used=set()
        for b in f.b1:
          base,legs=f.rawdata[b]; used.update(base)
          for l,m,r in legs: used.update(l+m+r)
        used=sorted(used); phis=[f.index(*b) for b in bonds]
        solver=Refine(f.aug); cols=[]
        for col,(j,phase) in enumerate(phis):
          rhs=[0]*f.aug.n; rhs[f.em[j]]=conj(phase)
          x=solver.solve(rhs)
          residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
          for row,(i,ph) in enumerate(phis): C[row,col]+=ph*x[f.em[i]]/nchar
          w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n]); cols.append([w[f.index(*e)[0]] for e in used])
        rows.append((f.ph,used,cols))
        print('SECTOR',iy,iz,'seconds',time.time()-start,flush=True)
        del solver,x,w; gc.collect()
    C=(C+C.H)/2; S=C**-1
    base=perturbation(mp.mpf(0),1,pls,bonds,side)
    def A(t,charge=1): return S+perturbation(t,charge,pls,bonds,side)-base
    root=mp.findroot(lambda t:mp.eighe(A(t),eigvals_only=True)[0],
      (mp.mpf('1.19'),mp.mpf('1.22')),tol=mp.power(10,-dps+12),verify=True)
    vals,V=mp.eighe(A(root)); v=V[:,0]
    drive=-(perturbation(root,1,pls,bonds,side)-base)*v
    compressed=[]
    for ph,used,cols in rows:
      compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
    all_targets=[b for b in f.b1 if b[1]==1]
    assert len(all_targets)==4*q*(R+1)
    targets=list(enumerate(all_targets))[start_row:stop_row]
    profile=[]
    for j,b in targets:
      sector=[]
      if not direct_only:
        for ph,used,values in compressed:
          sector.append((ph,f.rawjet(b,{e:values[i]*ph[0]**(e[0][1]//2)*ph[1]**(e[0][2]//2)
            for i,e in enumerate(used)})[2]))
      direct=mp.mpf(0); maxcell=mp.mpf(0)
      for cy in range(4*q):
        for cz in range(4*q):
          field={e:mp.mpc(0) for e in compressed[0][1]}
          for ph,used,values in compressed:
            for e,zv in zip(used,values):
              x,d=e
              field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*zv/nchar
          cell=f.rawjet(b,field)[2]
          direct+=cell; maxcell=max(maxcell,abs(cell))
      four=2*sum(jj for ph,jj in sector)/nchar if not direct_only else mp.mpf(0)
      profile.append({'j':j,'x':b[0][0],'areaSum_direct':2*direct,
        'areaSum_Fourier':four,'max_cell_over_abs_sum':maxcell/max(abs(direct),mp.power(10,-dps+5)),
        'dictionary_relative_error':abs(2*direct-four)/max(abs(four),mp.power(10,-dps+5)) if not direct_only else mp.mpf(0),
        'sector_areaSum':[2*jj for ph,jj in sector]})
      print('ROW',j,'x',b[0][0],'area',mp.nstr(2*direct,12),'seconds',time.time()-start,flush=True)
    result={'q':q,'R':R,'side':side,'dps':dps,'root':root,'charged_low':list(vals[:4]),
      'flat_resolvent_absolute_residual':residual,'profile':profile,
      'signs':[mp.sign(x['areaSum_direct']) for x in profile],
      'start_row':start_row,'stop_row':stop_row,'direct_only':direct_only,
      'seconds':time.time()-start,
      'qualification':'Non-interval numerical evidence only; no Lean identification or proof.'}
    target=OUT/f'row_profile_right_q{q}_R{R}_p{dps}_{tag}.json'
    target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('SUMMARY',json.dumps(jsonable({k:v for k,v in result.items() if k!='profile'}),indent=2),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--q',type=int,default=1); p.add_argument('--R',type=int,default=20)
    p.add_argument('--dps',type=int,default=40); p.add_argument('--start',type=int,default=0)
    p.add_argument('--stop',type=int,default=10**9); p.add_argument('--direct-only',action='store_true')
    p.add_argument('--tag',default='all')
    a=p.parse_args(); run(a.q,a.R,a.dps,a.start,a.stop,a.direct_only,a.tag)
