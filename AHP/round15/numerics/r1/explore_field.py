#!/usr/bin/env python3
"""Diagnostic: reconstruct one right-star character and inspect its flat-collar field.
Numerical evidence only; no Lean claims. Writes only beside this script.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,Refine,mp,conj,jsonable
import argparse,json,re,resource,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def mpc_string(s):
    parts=s.strip().strip('()').split()
    if len(parts)==2:
        real,imag=parts[0],parts[1][:-1]
    elif len(parts)==3:
        real,imag=parts[0],parts[1]+parts[2][:-1]
    else:
        raise ValueError(s)
    return mp.mpc(mp.mpf(real),mp.mpf(imag))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--q',type=int,default=1); ap.add_argument('--R',type=int,default=22)
    ap.add_argument('--iy',type=int,default=0); ap.add_argument('--iz',type=int,default=1)
    ap.add_argument('--dps',type=int,default=50)
    ap.add_argument('--drive',default=str(ROOT/'AHP/round14/cancellation/r2/structure_right_q1_R22_p40.json'))
    a=ap.parse_args(); mp.mp.dps=a.dps
    raw=json.loads(Path(a.drive).read_text()); drive=[mpc_string(s) for s in raw['z']]
    q,R=a.q,a.R; start=time.time(); f=Family(q,R,mp.mpf(0),a.iy,a.iz,1).assemble()
    out,_=f.plaq('out',0)
    for i,row in enumerate(out.r):
        if i in f.em:
            for j,v in row.items():
                if j in f.em:f.aug.put(f.em[i],f.em[j],v)
    boundary=q*(12*R+12)
    # Independent copy of the right-star bond order.
    pls=[]
    for mu in [1,2]:
        for shift in [0,-1]:
            x=[boundary-1,0,0];x[mu]=shift;x=tuple(x)
            inside=(boundary,x[1],x[2]);xn=list(x);xn[mu]+=1;xn=tuple(xn)
            pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    bonds=list(dict.fromkeys(p[i] for p in pls for i in [0,2,3]))
    assert len(bonds)==len(drive)==9
    phis=[f.index(*b) for b in bonds];solver=Refine(f.aug)
    w=[mp.mpc(0)]*len(f.bonds);residual=mp.mpf(0)
    for col,(j,phase) in enumerate(phis):
        rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase);x=solver.solve(rhs)
        residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
        one=f.dressed(x[:f.n],x[f.n:f.n+f.H.n])
        for k in range(len(w)):w[k]+=drive[col]*one[k]
    records=[]
    for bond in f.bonds:
        xx,d=bond
        if f.s-6<=xx[0]<f.hi+1:
            j,ph=f.index(*bond)
            records.append({'x':xx[0],'direction':d,'bond':[list(xx),d],
                'w':w[j] if j<len(w) else 0,'u':x[f.em[j]] if j in f.em else 0,
                'phase':ph})
    result={'q':q,'R':R,'character':[a.iy,a.iz],'s':f.s,'hi':f.hi,
        'absolute_residual':residual,'records':records,'seconds':time.time()-start,
        'qualification':'Non-interval diagnostic only; drive imported from round-14 numerical data.'}
    target=OUT/f'field_q{q}_R{R}_c{a.iy}_{a.iz}.json'
    target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    for r in records:print(r['x'],r['direction'],mp.nstr(r['w'],18),mp.nstr(r['u'],18))
    print('RESIDUAL',mp.nstr(residual,8),'seconds',time.time()-start,'output',target)
if __name__=='__main__':main()
