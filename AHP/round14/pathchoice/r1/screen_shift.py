#!/usr/bin/env python3
"""Evidence for fine transverse placements of the original right star.

The carrier, crossing vector and drive are translated, so their spectra are
unchanged.  One direct dressed solve per character suffices for all placements.
Even shifts are permutation controls; odd shifts change the even-topIdx
aggregate.  Double precision only, with no interval or Lean claim.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
from probe import Family,mp,np
from screen_signed import geometry,local
import itertools,json,pickle,resource,time,gc
from scipy.optimize import brentq
from scipy.sparse.linalg import splu
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def embed(pls,bonds,t,charge=1):
    ans=np.zeros((len(bonds),len(bonds)),complex)
    for p in pls:
        m=local([0,t,0,0],charge)
        for i in [0,2,3]:
            for j in [0,2,3]:ans[bonds.index(p[i]),bonds.index(p[j])]+=m[i,j]
    return ans

def run(q,R,shifts):
    start=time.time();mp.mp.dps=30;lo=q*(12*R+12);nc=(4*q)**2
    cache=OUT/f'flat_cache_q{q}_R{R}.pkl'
    with cache.open('rb') as h:saved=pickle.load(h)
    C=saved['C'];C=(C+C.conj().T)/2;S=np.linalg.inv(C)
    pls0,bonds0=geometry(lo);n=len(bonds0);base=embed(pls0,bonds0,0)
    def delta(t,charge=1):return embed(pls0,bonds0,t,charge)-base
    def mat(t,charge=1):return S+delta(t,charge)
    def low(t):return float(np.linalg.eigvalsh(mat(t))[0])
    root=brentq(low,1.19,1.22,xtol=1e-14);ev,V=np.linalg.eigh(mat(root));v=V[:,0]
    drive=-delta(root)@v
    # Every placement uses the translated flat response of this same drive.
    rows={s:[] for s in shifts};residual=0.
    for iy in range(4*q):
        for iz in range(4*q):
            f=Family(q,R,mp.mpf(0),iy,iz,1).assemble();out,_=f.plaq('out',0)
            for i,row in enumerate(out.r):
                if i in f.em:
                    for j,val in row.items():
                        if j in f.em:f.aug.put(f.em[i],f.em[j],val)
            targets=[((f.s-2,0,0),d) for d in range(3)];used=set()
            for b in targets:
                b0,legs=f.rawdata[b];used.update(b0)
                for l,m,r in legs:used.update(l+m+r)
            used=sorted(used);phis=[f.index(*b) for b in bonds0]
            rhs=np.zeros(f.aug.n,complex)
            for coeff,(j,phase) in zip(drive,phis):rhs[f.em[j]]+=coeff*phase.conjugate()
            A=f.aug.scipy();sol=splu(A).solve(rhs)
            residual=max(residual,float(np.max(np.abs(A@sol-rhs))))
            w=f.dressed(list(sol[:f.n]),list(sol[f.n:f.n+f.H.n]))
            for sy,sz in shifts:
                values=[]
                for (x,y,z),d in used:
                    values.append(w[f.index((x,y-sy,z-sz),d)[0]])
                rows[(sy,sz)].append(((complex(f.ph[0]),complex(f.ph[1])),used,values))
            print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
            gc.collect()
    reports=[]
    for shift in shifts:
        cells=[[] for _ in range(3)]
        for cy in range(4*q):
            for cz in range(4*q):
                field={e:0j for e in rows[shift][0][1]}
                for ph,used,values in rows[shift]:
                    for e,z in zip(used,values):
                        x,d=e;field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
                for d,b in enumerate(targets):cells[d].append(complex(f.rawjet(b,field)[2]))
        sums=[sum(c) for c in cells];maxima=[max(map(abs,c)) for c in cells];l1=[sum(map(abs,c)) for c in cells]
        reports.append({'shift':shift,'root':root,'charged_low':list(map(float,ev[:4])),
            'first_physical_top_jet_sums':sums,'max_abs_first_top_jet':maxima,
            'l1_abs_first_top_jet':l1,'max_over_abs_sum':[m/abs(s) if s else None for m,s in zip(maxima,sums)],
            'abs_sum_over_l1':[abs(s)/a if a else None for s,a in zip(sums,l1)],
            'first_top_jet_cells':cells})
        print('SHIFT',shift,'ratios',reports[-1]['max_over_abs_sum'],'jets',sums,flush=True)
    result={'q':q,'R':R,'root':root,'flat_resolvent_absolute_residual':residual,
        'placements':reports,'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'Double-precision non-interval evidence only. The same original right-star crossing drive is translated by fine transverse shifts; all-character direct full augmented dressed solves and exact Taylor jets. Even shifts are aggregate permutation controls. No P1/P2/KernelLine translation theorem, spectral enclosure, Lean dictionary, or cofinal claim.'}
    def clean(x):
        if isinstance(x,(complex,np.complex128)):return [float(x.real),float(x.imag)]
        if isinstance(x,np.floating):return float(x)
        if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [clean(v) for v in x]
        return x
    target=OUT/f'shifts_q{q}_R{R}.json';target.write_text(json.dumps(clean(result),indent=2)+'\n')
    print('WROTE',target,flush=True)

if __name__=='__main__':run(2,20,list(itertools.product(range(4),repeat=2)))
