#!/usr/bin/env python3
"""Independent R2 source-family check: held-out q4 R20, new source locations.
Full neutral KKT solve versus a hyperbolic Green kernel (not the author's
Thomas algorithm). Evidence only; Jprime=Delta_flat profile is not proved here.
"""
import os, sys, resource, json, time, argparse
from pathlib import Path
sys.dont_write_bytecode = True
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
ROOT=Path(__file__).resolve().parents[5]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family, Sp, Refine, mp, jsonable
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
parser=argparse.ArgumentParser(); parser.add_argument('--dps',type=int,required=True)
mp.mp.dps=parser.parse_args().dps
t0=time.time()
f=Family(4,20,mp.mpf(0),charge=0).assemble()
N=(f.s-f.p)//2
delta,_=f.plaq()
na=f.aug.n; Q=f.Q; nc=Q.n
system=Sp(na+nc,na+nc)
system.block(f.aug,0,0); system.block(Q,na,0); system.block(Q.star(),0,na)
solver=Refine(system)
gamma=mp.acosh(3)
def green(j,k):
    if not 0<=k<N: return mp.mpf(0)
    return (-1)**(j+k)*mp.sinh((min(j,k)+1)*gamma)*mp.sinh((N-max(j,k))*gamma)/(mp.sinh(gamma)*mp.sinh((N+1)*gamma))
rows=[]
# Deliberately not i=0,1,N/2,N-1 used by the author.
for i in [2,N//3,N-2]:
    profile=[mp.mpf(0)]*len(f.bonds)
    profile[f.bi[((f.p+2*i,0,0),1)]]=1
    J=delta.apply(profile)
    rhs=[J[j] for j in f.e]+[mp.mpf(0)]*(na+nc-f.n)
    sol=solver.solve(rhs)
    actual=sol[na+len(f.b0):]
    a=[mp.mpf(3)/2*green(j,i)+mp.mpf(1)/2*green(j,i-1) for j in range(N)]
    weights=[mp.mpf(int(j==i)-int(j+1==i))-2*(a[j-1] if j else 0)+2*(a[j+1] if j+1<N else 0) for j in range(N)]
    predicted=[mp.mpf(0)]*len(f.b1)
    for j,h in enumerate(weights): predicted[3*j+2]=h
    err=max(abs(x-y) for x,y in zip(actual,predicted))
    residual=max(map(abs,[x-y for x,y in zip(system.apply(sol),rhs)]))
    row=dict(q=4,R=20,N=N,source_index=i,dps=mp.mp.dps,
             max_dictionary_error=err,max_other_direction=max(abs(z) for j,z in enumerate(actual) if j%3!=2),
             full_kkt_residual=residual,source_norm=max(map(abs,actual)),
             selected_weight_actual=actual[3*i+2],selected_weight_predicted=weights[i])
    rows.append(row)
    print('SOURCE',i,'ERROR',mp.nstr(err,8),'KKT_RESIDUAL',mp.nstr(residual,8),flush=True)
out=dict(rows=rows,seconds=time.time()-t0,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         qualification='floating-point only; no interval enclosure, no spectral screen; flat source identification not a Lean theorem')
p=Path(__file__).resolve().parent/f'source_q4_R20_p{mp.mp.dps}.json'
p.write_text(json.dumps(jsonable(out),indent=2)+'\n')
print('RESULT',p,flush=True)
