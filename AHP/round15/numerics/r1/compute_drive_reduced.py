#!/usr/bin/env python3
"""D4-reduced right-star Schur drive, using exact flat-resolvent covariance.
The eight transverse operations are y/z swap and independent sign flips. Only
one flat solve per D4 character orbit is needed. Numerical evidence only.
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
from right_star import geometry,perturbation
import argparse,json,time,resource,gc,itertools
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def operations(N):
    # name, character map, site map, direction map, conjugate
    ans=[]
    for sw,ny,nz in itertools.product([0,1],repeat=3):
        def cm(c,sw=sw,ny=ny,nz=nz,N=N):
            y,z=c
            if sw:y,z=z,y
            if ny:y=(-y)%N
            if nz:z=(-z)%N
            return y,z
        def sm(x,sw=sw,ny=ny,nz=nz):
            a,b,c=x
            if sw:b,c=c,b
            if ny:b=-b
            if nz:c=-c
            return a,b,c
        dm=[0,2,1] if sw else [0,1,2]
        ans.append((f'sw{sw}_ny{ny}_nz{nz}',cm,sm,dm,bool(ny^nz)))
    return ans

def run(q,R,dps):
    mp.mp.dps=dps;start=time.time();N=4*q;nchar=N*N;boundary=q*(12*R+12)
    pls,bonds=geometry(boundary,'right');n=len(bonds);C=mp.matrix(n);residual=mp.mpf(0)
    ops=operations(N);remaining=set(itertools.product(range(N),repeat=2));orbits=[]
    while remaining:
        rep=min(remaining);iy,iz=rep
        f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
        out,_=f.plaq('out',0)
        for i,row in enumerate(out.r):
            if i in f.em:
                for j,v in row.items():
                    if j in f.em:f.aug.put(f.em[i],f.em[j],v)
        phis=[f.index(*b) for b in bonds];solver=Refine(f.aug);M=mp.matrix(n)
        for col,(j,phase) in enumerate(phis):
            rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(phase);x=solver.solve(rhs)
            residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(x),rhs)))
            for row,(i,ph) in enumerate(phis):M[row,col]+=ph*x[f.em[i]]
        covered=[]
        old_phase={b:ph for b,(i,ph) in zip(bonds,phis)}
        def new_phase(c,b):
            x,d=b
            return (mp.exp(2j*mp.pi*c[0]/N)**(x[1]//2)*
                    mp.exp(2j*mp.pi*c[1]/N)**(x[2]//2))
        def map_bond(b,sm,dm):
            x,d=b;candidate=(sm(x),dm[d])
            if candidate in bonds:return candidate
            (a,y,z),dd=candidate
            for dy in [0,2,-2]:
                for dz in [0,2,-2]:
                    trial=((a,y+dy,z+dz),dd)
                    if trial in bonds:return trial
            raise ValueError(('unmapped bond',candidate))
        for name,cm,sm,dm,doconj in ops:
            other=cm(rep);covered.append(other)
            mapped=[map_bond(b,sm,dm) for b in bonds]
            assert len(set(mapped))==n
            for i in range(n):
                for j in range(n):
                    z=M[i,j]
                    if doconj:z=conj(z)
                    row_ratio=new_phase(other,mapped[i])/old_phase[bonds[i]]
                    if doconj:
                        col_ratio=conj(new_phase(other,mapped[j]))/old_phase[bonds[j]]
                    else:
                        col_ratio=conj(new_phase(other,mapped[j]))/conj(old_phase[bonds[j]])
                    C[bonds.index(mapped[i]),bonds.index(mapped[j])]+=row_ratio*col_ratio*z/nchar
        assert set(covered)<=remaining
        remaining.difference_update(covered);orbits.append({'representative':rep,'size':len(set(covered)),'characters':sorted(set(covered))})
        print('ORBIT',rep,'size',len(set(covered)),'remaining',len(remaining),'seconds',time.time()-start,flush=True)
        del solver,x,M;gc.collect()
    assert not remaining
    asym=mp.mnorm(C-C.H,1);C=(C+C.H)/2;S=C**-1
    base=perturbation(mp.mpf(0),1,pls,bonds,'right')
    def A(t):return S+perturbation(t,1,pls,bonds,'right')-base
    root=mp.findroot(lambda t:mp.eighe(A(t),eigvals_only=True)[0],
      (mp.mpf('1.19'),mp.mpf('1.22')),tol=mp.power(10,-dps+12),verify=True)
    vals,V=mp.eighe(A(root));v=V[:,0];drive=-(perturbation(root,1,pls,bonds,'right')-base)*v
    result={'q':q,'R':R,'dps':dps,'root':root,'charged_low':list(vals[:4]),
      'C':[[C[i,j] for j in range(n)] for i in range(n)],'eigenvector':list(v),'z':list(drive),
      'orbits':orbits,'flat_resolvent_absolute_residual':residual,
      'compressed_resolvent_hermitian_error':asym,'boundary_null_residual':mp.mnorm(A(root)*v,1),
      'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      'qualification':'Non-interval numerical evidence only; D4 orbit reduction of full flat augmented resolvent.'}
    target=OUT/f'drive_reduced_right_q{q}_R{R}_p{dps}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('SUMMARY',json.dumps(jsonable({k:v for k,v in result.items() if k not in ['C','eigenvector','z','orbits']}),indent=2),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,required=True);ap.add_argument('--R',type=int,required=True);ap.add_argument('--dps',type=int,default=40)
    a=ap.parse_args();run(a.q,a.R,a.dps)
