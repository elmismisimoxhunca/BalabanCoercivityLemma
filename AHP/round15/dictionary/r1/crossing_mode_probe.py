#!/usr/bin/env python3
"""Reconstruct a right-star crossing generator and project its collar modes.

The drive is read from the completed structure probe; no root is refitted and no
numerical value is used as a Lean premise.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj
sys.path.insert(0,str(ROOT/'AHP/round14/cancellation/r1'))
from structure_probe import geometry
import argparse,json,resource,numpy as np
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent
CELLS=[(0,0),(1,0),(0,1),(1,1)]

def run(q,R,iy,iz,dps):
    mp.mp.dps=dps
    if R==20:source=ROOT/'AHP/round14/cancellation/r1/structure_right_q1_R20_p50.json'
    elif R==22:source=ROOT/'AHP/round14/cancellation/r2/structure_right_q1_R22_p40.json'
    else:raise ValueError('completed drive currently available for R=20,22')
    old=json.loads(source.read_text());drive=[mp.mpc(complex(z.replace(' ',''))) for z in old['z']]
    f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
    out,_=f.plaq('out',0)
    for i,row in enumerate(out.r):
      if i in f.em:
       for j,v in row.items():
        if j in f.em:f.aug.put(f.em[i],f.em[j],v)
    boundary=q*(12*R+12);pls,bonds=geometry(boundary,'right');phis=[f.index(*b) for b in bonds]
    # Match the completed high-precision drive column-by-column.  This avoids
    # losing the small physical residual in a single ill-conditioned summed solve.
    solver=Refine(f.aug);sol=[mp.mpc(0)]*f.aug.n;residual=mp.mpf(0);wcols=[]
    for col,(j,phase) in enumerate(phis):
      rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase)
      x=solver.solve(rhs)
      residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
      sol=[v+drive[col]*xv for v,xv in zip(sol,x)]
      wcols.append(f.dressed(x[:f.n],x[f.n:f.n+f.H.n]))
    w=[sum(wcols[col][i]*drive[col] for col in range(len(drive))) for i in range(len(wcols[0]))]
    # Reproduce this character's contribution to the independently retained area.
    layer=f.s-2;targets=[((layer,0,0),d) for d in range(3)]
    used=set()
    for b in targets:
      base,legs=f.rawdata[b];used.update(base)
      for l,m,r in legs:used.update(l+m+r)
    used=sorted(used)
    field={e:w[f.index(*e)[0]]*f.index(*e)[1] for e in used}
    sector_jets=[f.rawjet(b,field)[2] for b in targets]
    old_sector=mp.mpf(old['sector_jets'][4*iy+iz])
    sector_error=abs(2*sector_jets[1]-2*old_sector)/max(abs(2*old_sector),mp.power(10,-dps+5))
    # Exact collar block data and reduced recurrence.
    def var(x,y,z,d):return f.em.get(f.bi[((x,y,z),d)])
    def entry(x,a,d,y,b,e):
        ya,za=CELLS[a];yb,zb=CELLS[b];i,j=var(x,ya,za,d),var(y,yb,zb,e)
        return f.K.r[i].get(j,0) if i is not None and j is not None else 0
    order=[(a,d) for d in range(3) for a in range(4)]
    def mat(x,dx):return np.array([[complex(entry(x,a,d,x+dx,b,e)) for b,e in order] for a,d in order])
    x0=f.s+2;A,B,C=mat(x0,1),mat(x0,0),mat(x0,-1)
    A00,A01,A10,A11=A[:4,:4],A[:4,4:],A[4:,:4],A[4:,4:]
    B00,B01,B10,B11=B[:4,:4],B[:4,4:],B[4:,:4],B[4:,4:]
    C00,C01,C10,C11=C[:4,:4],C[:4,4:],C[4:,:4],C[4:,4:]
    ar=A11-B10@np.linalg.inv(B00)@A01
    br=B11-B10@np.linalg.inv(B00)@B01-C10@np.linalg.inv(B00)@A01
    cr=C11-C10@np.linalg.inv(B00)@B01
    T=np.block([[-np.linalg.solve(ar,br),-np.linalg.solve(ar,cr)],[np.eye(8),np.zeros((8,8))]])
    def vec(x):
        ans=[]
        for a,d in order:
          y,z=CELLS[a];i=var(x,y,z,d);ans.append(complex(sol[i]) if i is not None else 0)
        return np.array(ans)
    def state(x):
        v0,v1=vec(x-1),vec(x)
        # The reduced coordinates are only the eight transverse components.
        w0,w1=v0[4:],v1[4:]
        return np.concatenate([w1,w0])
    recurrence_errors=[]
    for x in range(f.s+2,f.hi-1):
        v0,v1,v2=vec(x-1),vec(x),vec(x+1)
        val=np.linalg.norm(A@v2+B@v1+C@v0)/max(np.linalg.norm(v1),1e-300)
        recurrence_errors.append(val)
    transfer_error=np.linalg.norm(T@state(f.s+2)-state(f.s+3))/max(np.linalg.norm(state(f.s+3)),1e-300)
    ev,V=np.linalg.eig(T);seed=state(f.s+2);coef=np.linalg.solve(V,seed)
    mode_records=[]
    for k,lam in enumerate(ev):
        y=lam+1/lam
        mode_records.append({'index':k,'lambda':complex(lam),'abs_lambda':float(abs(lam)),
          'y':complex(y),'coefficient':complex(coef[k]),'coefficient_norm':float(abs(coef[k])),
          'seed_mode_norm':float(np.linalg.norm(coef[k]*V[:,k]))})
    # Compare the complete modal reconstruction to the next state and report the
    # dominant branch at the star side, without dropping any branch.
    modal_next=V@np.diag(ev)@coef
    modal_error=np.linalg.norm(modal_next-state(f.s+3))/max(np.linalg.norm(state(f.s+3)),1e-300)
    result={'q':q,'R':R,'character':[iy,iz],'source':str(source),'dps':dps,
      'actual_augmented_residual':residual,'sector_areaSum':2*sector_jets[1],
      'retained_sector_areaSum':2*old_sector,'sector_relative_error':sector_error,
      'deep_recurrence_relative_errors':recurrence_errors,'max_deep_recurrence_relative_error':max(recurrence_errors),
      'transfer_one_step_relative_error':transfer_error,'modal_one_step_relative_error':modal_error,
      'mode_seed_x':f.s+2,'mode_records':mode_records,
      'qualification':'Non-interval numerical evidence only. The drive and area are checked against retained completed work. No Lean identification is asserted.'}
    target=OUT/f'crossing_q{q}_R{R}_c{iy}_{iz}.json'
    target.write_text(json.dumps(result,default=lambda z:str(z),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='mode_records'},default=lambda z:str(z),indent=2))
    print('MODES',json.dumps(mode_records,default=lambda z:str(z),indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=20)
    p.add_argument('--iy',type=int,default=1);p.add_argument('--iz',type=int,default=0);p.add_argument('--dps',type=int,default=50)
    a=p.parse_args();run(a.q,a.R,a.iy,a.iz,a.dps)
