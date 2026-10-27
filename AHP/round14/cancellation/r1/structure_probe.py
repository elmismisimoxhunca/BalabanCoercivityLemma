#!/usr/bin/env python3
"""Numerical structure probe for the mixed-colour area form. Evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
import argparse,json,time,resource,gc
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def geometry(lo,side):
    pls=[]
    for mu in [1,2]:
      for shift in [0,-1]:
        x=[lo-1,0,0]; x[mu]=shift; x=tuple(x)
        inside=(lo,x[1],x[2]); xn=list(x); xn[mu]+=1; xn=tuple(xn)
        pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    active=[0,1,2] if side=='left' else [0,2,3]
    bonds=list(dict.fromkeys(p[i] for p in pls for i in active))
    return pls,bonds

def perturbation(t,charge,pls,bonds,side):
    result=mp.matrix(len(bonds))
    for p in pls:
      co,si=mp.cos(t),(-1 if side=='left' else 1)*mp.sin(t)
      cs=[mp.mpf(1),mp.mpf(1),-mp.exp(2j*charge*t) if side=='left' else mp.mpf(-1),mp.mpf(-1)]
      local=mp.matrix([[co*conj(cs[i])*cs[j] for j in range(4)] for i in range(4)])
      order=[2,3,0,1]
      if charge:
        for a in range(4):
          for b in range(a+1,4):
            i,j=order[a],order[b]; v=-1j*si*conj(cs[i])*cs[j]
            local[i,j]+=v; local[j,i]+=conj(v)
      active=[0,1,2] if side=='left' else [0,2,3]
      for i in active:
        for j in active: result[bonds.index(p[i]),bonds.index(p[j])]+=local[i,j]
    return result

def run(q,R,dps,side):
    mp.mp.dps=dps; start=time.time(); nchar=(4*q)**2
    boundary=4*q if side=='left' else q*(12*R+12)
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
        layer=f.p if side=='left' else f.s-2
        targets=[((layer,0,0),d) for d in range(3)]
        used=set()
        for b in targets:
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
    # Reconstruct each physical dressed atom at every transverse cell, exactly as
    # in star_crosscheck.py, then evaluate the genuine two-atom neutral jet.
    K=mp.matrix(n)
    for cy in range(4*q):
      for cz in range(4*q):
        physical=[]
        for alpha in range(n):
          field={e:mp.mpc(0) for e in rows[0][1]}
          for ph,used,cols in rows:
            for e,z in zip(used,cols[alpha]):
              x,d=e
              field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nchar
          physical.append(field)
        for a in range(n):
          for b in range(a+1,n):
            field={e:1j*physical[a][e]+physical[b][e] for e in physical[a]}
            k=f.rawjet(targets[1],field)[2]
            K[a,b]+=k; K[b,a]-=k
      print('AREA CELL',cy,'seconds',time.time()-start,flush=True)
    # i*K is Hermitian and areaSum = z^* (iK) z.
    H=mp.matrix(n)
    for a in range(n):
      for b in range(n): H[a,b]=1j*K[a,b]
    ev=mp.eighe(H,eigvals_only=True)
    # The physical generator is the resolvent applied to the star drive, not
    # the nine-component Schur vector itself.
    drive=-(perturbation(root,1,pls,bonds,side)-base)*v
    z=drive
    area=mp.re((z.H*H*z)[0])
    # Independent direct cell evaluation for the crossing vector.
    compressed=[]
    for ph,used,cols in rows:
      compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
    direct=mp.mpf(0)
    sector_jets=[]
    for ph,used,values in compressed:
      sector_jets.append((ph,f.rawjet(targets[1],
        {e:values[i]*ph[0]**(e[0][1]//2)*ph[1]**(e[0][2]//2)
          for i,e in enumerate(used)})[2]))
    for cy in range(4*q):
      for cz in range(4*q):
        field={e:mp.mpc(0) for e in compressed[0][1]}
        for ph,used,values in compressed:
          for e,zv in zip(used,values):
            x,d=e
            field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*zv/nchar
        direct+=f.rawjet(targets[1],field)[2]
    result={'q':q,'R':R,'side':side,'dps':dps,'root':root,
      'charged_low':list(vals[:min(4,n)]),'areaSum_from_Hermitian':area,
      'two_physicalJetAggregate_direct':2*direct,
      'two_physicalJetAggregate_Fourier':2*sum(j for ph,j in sector_jets)/nchar,
      'sector_jets':[j for ph,j in sector_jets],
      'relative_area_dictionary_error':abs(area-2*direct)/max(abs(area),mp.power(10,-dps+5)),
      'hermitian_eigenvalues':list(ev),'boundary_null_residual':mp.mnorm(A(root)*v,1),
      'flat_resolvent_absolute_residual':residual,
      'K':[[K[a,b] for b in range(n)] for a in range(n)],
      'z':list(z),'seconds':time.time()-start,
      'qualification':'Non-interval numerical evidence only; no Lean identification or proof.'}
    target=OUT/f'structure_{side}_q{q}_R{R}_p{dps}.json'
    target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('SUMMARY',json.dumps(jsonable({k:v for k,v in result.items() if k not in ['K','z']}),indent=2),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--q',type=int,default=1); p.add_argument('--R',type=int,default=20)
    p.add_argument('--dps',type=int,default=50); p.add_argument('--side',choices=['left','right'],default='right')
    a=p.parse_args(); run(a.q,a.R,a.dps,a.side)
