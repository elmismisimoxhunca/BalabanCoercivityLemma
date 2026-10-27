#!/usr/bin/env python3
"""Round-14 held-out finite-star check, independent local plaquette assembly.
Full flat resolvents use all physical Fourier characters. Numerical evidence only.
Round-2 independent case: right-star q=1,R=30 was unused by the round-13/14 tracks.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
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
        x=[lo-1,0,0];x[mu]=shift;x=tuple(x)
        inside=(lo,x[1],x[2]);xn=list(x);xn[mu]+=1;xn=tuple(xn)
        # Standard plaquette boundary: normal, interior tangent, normal, exterior tangent.
        pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    active=[0,1,2] if side=='left' else [0,2,3]
    bonds=list(dict.fromkeys(p[i] for p in pls for i in active))
    return pls,bonds

def perturbation(t,charge,pls,bonds,side):
    result=mp.matrix(len(bonds))
    for p in pls:
      # Left: angles [0,0,0,t], holonomy=-t; right: [0,t,0,0], holonomy=t.
      co,si=mp.cos(t),(-1 if side=='left' else 1)*mp.sin(t)
      cs=[mp.mpf(1),mp.mpf(1),-mp.exp(2j*charge*t) if side=='left' else mp.mpf(-1),mp.mpf(-1)]
      local=mp.matrix([[co*conj(cs[i])*cs[j] for j in range(4)] for i in range(4)])
      order=[2,3,0,1]
      if charge:
        for a in range(4):
          for b in range(a+1,4):
            i,j=order[a],order[b];v=-1j*si*conj(cs[i])*cs[j]
            local[i,j]+=v;local[j,i]+=conj(v)
      active=[0,1,2] if side=='left' else [0,2,3]
      for i in active:
        for j in active:result[bonds.index(p[i]),bonds.index(p[j])]+=local[i,j]
    return result

def run(dps,side,q,R):
    if q <= 0 or R < 18 or R % 2:
        raise ValueError('require q>0, even R>=18')
    mp.mp.dps=dps;start=time.time();nchar=(4*q)**2
    boundary=4*q if side=='left' else q*(12*R+12)
    pls,bonds=geometry(boundary,side);n=len(bonds);C=mp.matrix(n)
    rows=[];residual=mp.mpf(0)
    for iy in range(4*q):
      for iz in range(4*q):
        f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
        out,_=f.plaq('out',0)
        for i,row in enumerate(out.r):
          if i in f.em:
            for j,v in row.items():
              if j in f.em:f.aug.put(f.em[i],f.em[j],v)
        layer=f.p if side=='left' else f.s-2
        targets=[((layer,0,0),d) for d in range(3)]
        used=set()
        for b in targets:
          base,legs=f.rawdata[b];used.update(base)
          for l,m,r in legs:used.update(l+m+r)
        used=sorted(used);phis=[f.index(*b) for b in bonds]
        solver=Refine(f.aug);cols=[]
        for col,(j,phase) in enumerate(phis):
          rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase)
          x=solver.solve(rhs)
          # Record actual absolute residual, not preconditioner stopping tolerance.
          residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
          for row,(i,ph) in enumerate(phis):C[row,col]+=ph*x[f.em[i]]/nchar
          w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n]);cols.append([w[f.index(*e)[0]] for e in used])
        rows.append((f.ph,used,cols))
        print('SECTOR',iy,iz,'seconds',time.time()-start,flush=True)
        del solver,x,w;gc.collect()
    asym=mp.mnorm(C-C.H,1);C=(C+C.H)/2;S=C**-1
    base=perturbation(mp.mpf(0),1,pls,bonds,side)
    def A(t,charge=1):return S+perturbation(t,charge,pls,bonds,side)-base
    root=mp.findroot(lambda t:mp.eighe(A(t),eigvals_only=True)[0],
      (mp.mpf('1.19'),mp.mpf('1.22')),tol=mp.power(10,-dps+12),verify=True)
    vals,V=mp.eighe(A(root));v=V[:,0]
    central=bonds.index(((boundary-1,0,0),0));leaves=[i for i in range(n) if i!=central]
    def restricted(t):return mp.eighe(mp.matrix([[A(t)[i,j] for j in leaves] for i in leaves]),eigvals_only=True)[0]
    drive=-(perturbation(root,1,pls,bonds,side)-base)*v
    compressed=[]
    for ph,used,cols in rows:
      compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
    sums=[mp.mpf(0)]*3;maximum=[mp.mpf(0)]*3
    rotations=[mp.mpc(1,1),mp.exp(mp.mpc(0,mp.mpf('0.37'))),mp.mpc(-2,3)]
    rotated_sums=[[mp.mpf(0)]*3 for _ in rotations]
    for cy in range(4*q):
      for cz in range(4*q):
        field={e:mp.mpc(0) for e in compressed[0][1]}
        for ph,used,values in compressed:
          for e,z in zip(used,values):
            x,d=e
            field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nchar
        for d,b in enumerate(targets):
          jet=f.rawjet(b,field)[2];sums[d]+=jet;maximum[d]=max(maximum[d],abs(jet))
          for ri,rot in enumerate(rotations):
            rotated_sums[ri][d]+=f.rawjet(b,{e:rot*z for e,z in field.items()})[2]
    # Right-star local stencil is affine in cos(t),sin(t). B is the flat form
    # with ONLY the four selected boundary plaquettes removed; P is PSD.
    P=base; B=S-P; K=perturbation(mp.pi/2,1,pls,bonds,side)
    pencil_errors=[]; monotone_mins=[]; prefix_mins=[]; restricted_mins=[]
    for i in range(1,16):
      t=mp.pi*i/32
      pencil_errors.append(mp.mnorm(A(t)-(B+mp.cos(t)*P+mp.sin(t)*K),1))
      monotone_mins.append(mp.eighe((mp.cos(t)*B+P)/mp.sin(t)**2,eigvals_only=True)[0])
      prefix_mins.append(mp.eighe(A(root*i/16),eigvals_only=True)[0])
      restricted_mins.append(restricted(t))
    result={'q':q,'R':R,'side':side,'top_layer':layer,'dps':dps,'root':root,'charged_low':list(vals[:4]),
      'neutral_spectrum_at_crossing':list(mp.eighe(A(root,0),eigvals_only=True)),
      'right_pencil_B_min':mp.eighe(B,eigvals_only=True)[0],
      'right_pencil_P_min':mp.eighe(P,eigvals_only=True)[0],
      'right_pencil_max_error':max(pencil_errors),
      'negative_scaled_derivative_min_15_angles':min(monotone_mins),
      'charged_prefix_min_15_angles':min(prefix_mins),
      'central_zero_min_15_angles':min(restricted_mins),
      'neutral_min_at_crossing':mp.eighe(A(root,0),eigvals_only=True)[0],
      'charged_min_at_pi':mp.eighe(A(mp.pi),eigvals_only=True)[0],
      'central_coordinate_abs':abs(v[central]),
      'central_zero_schur_min_at_0_root_halfpi':[restricted(t) for t in [mp.mpf(0),root,mp.pi/2]],
      'first_physical_top_jet_sums':sums,'max_abs_first_top_jet':maximum,
      'charged_line_scaled_jet_sums':rotated_sums,
      'charged_line_scaling_max_relative_error':max(abs(rotated_sums[ri][d]/(abs(rot)**2*sums[d])-1)
        for ri,rot in enumerate(rotations) for d in range(3)),
      'normalization':'unit nine-bond boundary vector, NOT unit full-carrier vector',
      'flat_resolvent_absolute_residual':residual,'compressed_resolvent_hermitian_error':asym,
      'boundary_null_residual':mp.mnorm(A(root)*v,1),
      'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      'qualification':'High-precision non-interval evidence only. Full flat augmented inverse before restriction; independently assembled four-edge local Hessians. No Lean stencil/DFT identification or cofinal theorem.'}
    target=OUT/f'star_{side}_q{q}_R{R}_p{dps}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('RESULT',json.dumps(jsonable(result),indent=2),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dps',type=int,required=True)
    p.add_argument('--side',choices=['left','right'],default='right')
    p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=30)
    a=p.parse_args();run(a.dps,a.side,a.q,a.R)
