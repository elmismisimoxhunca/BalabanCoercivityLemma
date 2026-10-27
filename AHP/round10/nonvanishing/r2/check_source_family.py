#!/usr/bin/env python3
"""Evidence only: full frozen-operator transcription versus generalized finite source.
No writes to prior rounds. No finite-curvature extrapolation: J'=Delta_flat f.
The latter identification is itself a dictionary obligation, not a Lean theorem here.
"""
import sys, os, resource, json, time
from pathlib import Path
sys.dont_write_bytecode = True
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
import probe
# probe's old limit is tightened before any family is allocated.
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
from probe import mp, Family, Sp, Refine, jsonable
mp.mp.dps=80
out=Path(__file__).resolve().parent
rows=[]
def tri_solve(rhs):
    N=len(rhs)
    piv=[mp.mpf(6)]*N
    f=list(rhs)
    for j in range(1,N):
        piv[j]=6-1/piv[j-1]
        f[j]-=f[j-1]/piv[j-1]
    a=[mp.mpf(0)]*N
    a[-1]=f[-1]/piv[-1]
    for j in range(N-2,-1,-1): a[j]=(f[j]-a[j+1])/piv[j]
    return a
for q,R in [(1,2),(2,2),(2,18),(4,18)]:
    t=time.time()
    f=Family(q,R,mp.mpf(0),charge=0).assemble()
    N=(f.s-f.p)//2
    delta,_=f.plaq()
    # Full augmented constrained solve, factor once then use exact flat sources.
    na=f.aug.n; Q=f.Q; nc=Q.n
    aug=Sp(na+nc,na+nc)
    aug.block(f.aug,0,0); aug.block(Q,na,0); aug.block(Q.star(),0,na)
    solver=Refine(aug)
    for i in [0,1,N//2,N-1]:
        field=[mp.mpf(0)]*len(f.bonds)
        field[f.bi[((f.p+2*i,0,0),1)]]=1
        J=delta.apply(field)
        rhs=[J[j] for j in f.e]+[0]*(na+nc-f.n)
        sol=solver.solve(rhs)
        actual=sol[na+len(f.b0):]
        arhs=[mp.mpf(0)]*N; arhs[i]=mp.mpf(3)/2
        if i:arhs[i-1]=mp.mpf(1)/2
        alpha=tri_solve(arhs)
        weights=[int(j==i)-int(j+1==i)-2*(alpha[j-1] if j else 0)
                 +2*(alpha[j+1] if j+1<N else 0) for j in range(N)]
        predicted=[mp.mpf(0)]*len(f.b1)
        for j,h in enumerate(weights):predicted[3*j+2]=h
        err=max(abs(a-b) for a,b in zip(actual,predicted))
        other=max(abs(a) for k,a in enumerate(actual) if k%3!=2)
        rows.append(dict(q=q,R=R,N=N,source_index=i,dps=mp.mp.dps,
            max_absolute_dictionary_error=err,max_other_direction_component=other,
            kkt_residual=solver.history[-1][-1],max_source_component=max(map(abs,actual)),
            first_four_predicted=weights[:4],first_four_actual=[actual[3*j+2] for j in range(4)]))
        print('SOURCE',q,R,i,'error',mp.nstr(err,6),'other',mp.nstr(other,6),flush=True)
    print('SECONDS',time.time()-t,flush=True)
report={'status':'floating-point evidence only; no interval certificate; no crossing mode solved',
        'Jprime_assumption':'flat localized plaquette Hessian applied to the neutral profile',
        'rows':rows,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(out/'source_family_check.json').write_text(json.dumps(jsonable(report),indent=2)+'\n')
