#!/usr/bin/env python3
"""Numerical diagnostic for the actual right-star flat collar.

Evidence only.  Reconstructs the q=1,R=22,c=(0,1) resolvent from the retained
round-14 drive and checks the integer f.K three-direction recurrence outside
Omega_1.  No result here is used as a Lean premise.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
import json,resource,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def mpc_string(s):
    if not isinstance(s,str): return mp.mpc(s)
    p=s.strip().strip('()').split()
    if len(p)==2: return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1][:-1]))
    return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1]+p[2][:-1]))

def main():
    dps=50; mp.mp.dps=dps; start=time.time()
    raw=json.loads((ROOT/'AHP/round14/cancellation/r2/structure_right_q1_R22_p40.json').read_text())
    drive=[mpc_string(s) for s in raw['z']]
    q,R,iy,iz=1,22,0,1
    f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
    out,_=f.plaq('out',0)
    for i,row in enumerate(out.r):
        if i in f.em:
            for j,v in row.items():
                if j in f.em: f.aug.put(f.em[i],f.em[j],v)
    boundary=q*(12*R+12)
    pls=[]
    for mu in [1,2]:
        for shift in [0,-1]:
            xx=[boundary-1,0,0];xx[mu]=shift;xx=tuple(xx)
            inside=(boundary,xx[1],xx[2]);xn=list(xx);xn[mu]+=1;xn=tuple(xn)
            pls.append([(xx,0),(inside,mu),(xn,0),(xx,mu)])
    bonds=list(dict.fromkeys(p[i] for p in pls for i in [0,2,3]))
    phis=[f.index(*b) for b in bonds]
    rhs=[mp.mpc(0)]*f.aug.n
    for (j,phase),z in zip(phis,drive): rhs[f.em[j]]=conj(phase)*z
    x=Refine(f.aug).solve(rhs)
    residual=max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs))
    w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n])
    records=[]
    for bond in f.bonds:
        xx,d=bond
        if xx[1]==0 and xx[2]==0 and f.s-4<=xx[0]<f.hi+1:
            j,ph=f.index(*bond)
            records.append({'x':xx[0],'direction':d,'bond':[list(xx),d],
                'w':w[j] if j<len(w) else 0,'u':x[f.em[j]] if j in f.em else 0,
                'phase':ph})
    by={(r['x'],r['direction']):mpc_string(r['u']) for r in records}
    km=[[0,0,0],[1,-1,0],[1,0,-1]]
    k0=[[5,-1,-1],[-1,5,-1],[-1,-1,5]]
    kp=[[0,1,1],[0,-1,0],[0,0,-1]]
    def mv(M,v): return [sum(M[i][j]*v[j] for j in range(3)) for i in range(3)]
    checks=[]
    for xx in range(f.s+2,f.hi-1):
        if not all((y,d) in by for y in [xx-1,xx,xx+1] for d in range(3)): continue
        vm=[by[xx-1,d] for d in range(3)]
        v=[by[xx,d] for d in range(3)]
        vp=[by[xx+1,d] for d in range(3)]
        rr=[mv(km,vm)[i]+mv(k0,v)[i]+mv(kp,vp)[i] for i in range(3)]
        scale=max(abs(z) for z in vm+v+vp)
        checks.append({'x':xx,'residual':rr,'scale':scale,
          'relative':max(abs(z) for z in rr)/scale if scale else 0})
    # The all-plaquette flat operator is f.K plus the omitted-plaquette block.
    # Extract its small longitudinal blocks in the genuinely flat collar.
    def var(xx,d): return f.em.get(f.bi[((xx,0,0),d)])
    def entry(xx,d,yy,e):
        i,j=var(xx,d),var(yy,e)
        if i is None or j is None: return mp.mpc(0)
        return f.K.r[i].get(j,0)+out.r[i].get(j,0)
    xrep=f.s+10
    all_blocks={str(dx):[[entry(xrep,d,xrep+dx,e) for e in range(3)] for d in range(3)]
      for dx in range(-2,3)}
    all_checks=[]
    am=[[entry(xrep,d,xrep-1,e) for e in range(3)] for d in range(3)]
    a0=[[entry(xrep,d,xrep,e) for e in range(3)] for d in range(3)]
    ap=[[entry(xrep,d,xrep+1,e) for e in range(3)] for d in range(3)]
    for xx in range(f.s+2,f.hi-1):
        if not all((y,d) in by for y in [xx-1,xx,xx+1] for d in range(3)): continue
        vm=[by[xx-1,d] for d in range(3)]
        v=[by[xx,d] for d in range(3)]
        vp=[by[xx+1,d] for d in range(3)]
        rr=[mv(am,vm)[i]+mv(a0,v)[i]+mv(ap,vp)[i] for i in range(3)]
        scale=max(abs(z) for z in vm+v+vp)
        all_checks.append({'x':xx,'residual':rr,'scale':scale,
          'relative':max(abs(z) for z in rr)/scale if scale else 0})
    aug_rows={str(d):[{'column':j,'value':v} for j,v in f.aug.r[var(xrep,d)].items()]
      for d in range(3)}
    aug_applied={str(d):f.aug.apply(x)[var(xrep,d)] for d in range(3)}
    # A single central-cell matrix element is NOT the Bloch-reduced block:
    # other transverse cells and directions contribute with their Bloch phases.
    # Group every raw column by longitudinal position and direction.
    reduced={str(dx):[[mp.mpc(0) for e in range(3)] for d in range(3)]
      for dx in range(-2,3)}
    bloch_error=mp.mpf(0)
    for bond in f.bonds:
        (xx,yc,zc),d=bond
        jglobal=f.bi[bond]
        if jglobal not in f.em: continue
        jlocal=f.em[jglobal]
        center=((xx,0,0),d)
        if center not in f.bi or f.bi[center] not in f.em: continue
        expected=f.index(*bond)[1]*x[f.em[f.bi[center]]]
        bloch_error=max(bloch_error,abs(x[jlocal]-expected))
    for d in range(3):
        i=var(xrep,d)
        for j,v in f.aug.r[i].items():
            if j>=f.n: continue
            (yy,yc,zc),e=f.bonds[f.e[j]]
            dx=yy-xrep
            if dx not in range(-2,3): continue
            phase=f.index((yy,yc,zc),e)[1]
            reduced[str(dx)][d][e]+=v*phase
    reduced_checks=[]
    for xx in range(f.s+2,f.hi-1):
        if not all((y,d) in by for y in [xx-1,xx,xx+1] for d in range(3)): continue
        vm=[by[xx-1,d] for d in range(3)]
        v=[by[xx,d] for d in range(3)]
        vp=[by[xx+1,d] for d in range(3)]
        rr=[mv(reduced['-1'],vm)[i]+mv(reduced['0'],v)[i]+mv(reduced['1'],vp)[i]
          for i in range(3)]
        scale=max(abs(z) for z in vm+v+vp)
        reduced_checks.append({'x':xx,'residual':rr,'scale':scale,
          'relative':max(abs(z) for z in rr)/scale if scale else 0})
    # The full per-character state has four transverse sublattice positions
    # (not one), hence 4*3=12 real-direction components.  This is the actual
    # constant-coefficient block in the flat collar, not the naive 3x3 block.
    cells=[(yc,zc) for yc in range(2) for zc in range(2)]
    def state(yc,zc,d): return (2*yc+zc)*3+d
    def varcell(xx,yc,zc,d): return f.em.get(f.bi[((xx,yc,zc),d)])
    reduced12={str(dx):[[mp.mpc(0) for _ in range(12)] for _ in range(12)]
      for dx in range(-2,3)}
    for yc,zc in cells:
        for d in range(3):
            i=varcell(xrep,yc,zc,d); row=state(yc,zc,d)
            for j,v in f.aug.r[i].items():
                if j>=f.n: continue
                (yy,yc2,zc2),e=f.bonds[f.e[j]]
                dx=yy-xrep
                if dx not in range(-2,3): continue
                reduced12[str(dx)][row][state(yc2,zc2,e)]+=v
    by12={(xx,yc,zc,d):x[varcell(xx,yc,zc,d)]
      for xx in range(f.s-4,f.hi+1) for yc,zc in cells for d in range(3)
      if varcell(xx,yc,zc,d) is not None}
    reduced12_checks=[]
    for xx in range(f.s+2,f.hi-1):
        rr=[]
        for yc,zc in cells:
            for d in range(3):
                row=state(yc,zc,d)
                value=mp.mpc(0)
                for dx,M in [(-1,reduced12['-1']),(0,reduced12['0']),(1,reduced12['1'])]:
                    for yc2,zc2 in cells:
                        for e in range(3):
                            value+=M[row][state(yc2,zc2,e)]*by12[xx+dx,yc2,zc2,e]
                rr.append((row,value))
        scale=max(abs(v) for v in by12.values())
        reduced12_checks.append({'x':xx,'residual':rr,'scale':scale,
          'relative':max(abs(v) for _,v in rr)/scale if scale else 0})
    # Generalized first-order eigenproblem E*y_{n+1}=F*y_n.
    import numpy as np
    from scipy.linalg import eig
    def npmat(M): return np.array([[complex(v) for v in row] for row in M],dtype=complex)
    am12,az12,ap12=map(npmat,[reduced12['-1'],reduced12['0'],reduced12['1']])
    E=np.zeros((24,24),dtype=complex); F=np.zeros((24,24),dtype=complex)
    E[:12,:12]=ap12; E[12:,12:]=np.eye(12)
    F[:12,:12]=-az12; F[:12,12:]=-am12; F[12:,:12]=np.eye(12)
    ev=eig(F,E,right=False,homogeneous_eigvals=False)
    ev=sorted([complex(z) for z in ev if np.isfinite(z)],key=lambda z:abs(z))
    result={'q':q,'R':R,'character':[iy,iz],'s':f.s,'hi':f.hi,'dps':dps,
      'absolute_resolvent_residual':residual,'records':records,'K_recurrence_checks':checks,
      'all_operator_reference_x':xrep,'all_operator_blocks':all_blocks,
      'aug_reference_rows':aug_rows,'aug_applied_at_reference':aug_applied,
      'all_recurrence_checks':all_checks,'bloch_relation_error':bloch_error,
      'reduced_operator_blocks':reduced,'reduced_recurrence_checks':reduced_checks,
      'reduced12_operator_blocks':reduced12,'reduced12_recurrence_checks':reduced12_checks,
      'reduced12_transfer_eigenvalues':[str(z) for z in ev],
      'reduced12_Aplus_determinant':str(np.linalg.det(ap12)),
      'seconds':time.time()-start,
      'qualification':'Non-interval numerical evidence only; f.K is not assumed to be the full effective collar operator.'}
    target=OUT/'collar_q1_R22_c0_1.json'
    target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    for c in checks:
        print('KCHECK',c['x'],mp.nstr(c['relative'],10))
    for c in all_checks:
        print('ALLCHECK',c['x'],mp.nstr(c['relative'],10))
    for c in reduced_checks:
        print('REDCHECK',c['x'],mp.nstr(c['relative'],10))
    for c in reduced12_checks:
        print('RED12CHECK',c['x'],mp.nstr(c['relative'],10))
    print('RED12_EIGENVALUES',ev)
    print('BLOCH_ERROR',mp.nstr(bloch_error,8))
    print('RESIDUAL',mp.nstr(residual,8),'seconds',time.time()-start,'output',target)
if __name__=='__main__': main()
