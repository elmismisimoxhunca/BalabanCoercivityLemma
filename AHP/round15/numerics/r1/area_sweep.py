#!/usr/bin/env python3
"""Per-character right-star top-row area and flat-collar profiles.
One flat solve per character and radius uses a previously computed nine-bond
Schur drive. Non-interval numerical evidence only; no Lean claim.
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
import argparse,json,time,resource,gc
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def mpc_string(s):
    p=s.strip().strip('()').split()
    if len(p)==2:return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1][:-1]))
    if len(p)==3:return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1]+p[2][:-1]))
    raise ValueError(s)

def solve_character(q,R,iy,iz,drive,bonds,dps):
    f=Family(q,R,mp.mpf(0),iy,iz,1).assemble();out,_=f.plaq('out',0)
    for i,row in enumerate(out.r):
        if i in f.em:
            for j,v in row.items():
                if j in f.em:f.aug.put(f.em[i],f.em[j],v)
    phis=[f.index(*b) for b in bonds];solver=Refine(f.aug)
    w=[mp.mpc(0)]*len(f.bonds);Y=[mp.mpc(0)]*f.aug.n;rhs_total=[mp.mpc(0)]*f.aug.n;residual=mp.mpf(0)
    # Keep the original nine-column convention. Besides avoiding a large
    # cancellation in one combined RHS, this is exactly the round-14 drive.
    for col,(j,phase) in enumerate(phis):
        rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase);x=solver.solve(rhs)
        residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
        one=f.dressed(x[:f.n],x[f.n:f.n+f.H.n])
        for k in range(len(w)):w[k]+=drive[col]*one[k]
        for k in range(f.aug.n):
            Y[k]+=drive[col]*x[k];rhs_total[k]+=drive[col]*rhs[k]
    target=(f.s-2,0,0),1;base,legs=f.rawdata[target];used=set(base)
    for l,m,r in legs:used.update(l+m+r)
    field={e:w[f.index(*e)[0]]*f.ph[0]**(e[0][1]//2)*f.ph[1]**(e[0][2]//2) for e in used}
    jet=f.rawjet(target,field)[2]
    # Small data suffice to test radial laws and to reconstruct top-row quadratic forms.
    values={}
    for xx in [f.s-2,f.s,f.s+2,f.hi-1]:
        for d in range(3):
            b=((xx,0,0),d);j,ph=f.index(*b);values[f'{xx}:{d}']=w[j]
    augmented=f.aug.apply(Y);by_x={}
    for i in range(f.n):
        xx=f.bonds[f.e[i]][0][0];by_x.setdefault(xx,[]).append(abs(augmented[i]-rhs_total[i]))
    for i in range(f.n,f.aug.n):
        k=i-f.n;site_index=k if k<f.H.n else k-f.H.n
        xx=f.sites[site_index][0];by_x.setdefault(xx,[]).append(abs(augmented[i]-rhs_total[i]))
    return {'character':[iy,iz],'sector_areaSum':2*jet,'sector_jet':jet,
      'interface_values':values,'flat_resolvent_absolute_residual':residual,
      'augmented_null_by_x':{str(x):max(v) for x,v in by_x.items()},
      'augmented_null_max':max((max(v) for v in by_x.values()),default=mp.mpf(0)),
      'target_layer':f.s-2}

def run(q,radii,dps,drive_path,chars):
    mp.mp.dps=dps;raw=json.loads(Path(drive_path).read_text());drive=[mpc_string(s) for s in raw['z']]
    assert len(drive)==9
    records=[];start=time.time()
    for R in radii:
        boundary=q*(12*R+12);_,bonds=geometry(boundary,'right');assert len(bonds)==9
        for iy,iz in chars:
            rec=solve_character(q,R,iy,iz,drive,bonds,dps);rec['R']=R;records.append(rec)
            print('CASE',q,R,iy,iz,'area',mp.nstr(rec['sector_areaSum'],12),'seconds',time.time()-start,flush=True)
            gc.collect()
    result={'q':q,'radii':radii,'dps':dps,'drive':str(drive_path),'root':raw['root'],
      'records':records,'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      'qualification':'Non-interval numerical evidence only; same imported nine-bond drive at each radius, full flat augmented solve.'}
    tag='_'.join(map(str,radii));target=OUT/f'area_sweep_right_q{q}_R{tag}_p{dps}.json'
    target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('OUTPUT',target,'seconds',time.time()-start)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,required=True);ap.add_argument('--radii',default='20,22,24')
    ap.add_argument('--dps',type=int,default=50);ap.add_argument('--drive',required=True);ap.add_argument('--chars',default='all')
    a=ap.parse_args();radii=[int(x) for x in a.radii.split(',')];N=4*a.q
    chars=[(iy,iz) for iy in range(N) for iz in range(N)] if a.chars=='all' else [tuple(map(int,s.split(':'))) for s in a.chars.split(',')]
    run(a.q,radii,a.dps,a.drive,chars)
