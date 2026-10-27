#!/usr/bin/env python3
"""Higher-precision dressed-solve replay of the alternating length-two candidate.

The small Schur crossing drive is still double precision.  Every full augmented
solve, residual, reconstruction and raw jet uses mpmath at the requested dps.
Thus this checks response/cell stability, not the root, P1/P2, or any theorem.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
from probe import Family,Refine,mp,np,conj,jsonable
from screen_long import axial,geometry,embed,original
import argparse,json,pickle,resource,time,gc
from scipy.optimize import brentq
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def run(dps):
    mp.mp.dps=dps;start=time.time();q,R=2,20;length=2;nc=(4*q)**2
    lo=q*(12*R+12);path_bonds=[axial(mu,k) for mu in [1,2] for k in range(-length,length)]
    pls,bonds=geometry(lo,path_bonds);n=len(bonds)
    with (OUT/'long_flat_q2_R20_L2_axial.pkl').open('rb') as h:saved=pickle.load(h)
    C=saved['C'];C=(C+C.conj().T)/2;S=np.linalg.inv(C)
    cmap=original()
    for b in [axial(1,1),axial(1,-2),axial(2,1),axial(2,-2)]:cmap[b]=-1
    coefficients=[float(cmap.get(b,0)) for b in path_bonds]
    base=embed(pls,bonds,coefficients,0)
    def delta(t,charge=1):return embed(pls,bonds,coefficients,t,charge)-base
    def mat(t):return S+delta(t)
    def low(t):return float(np.linalg.eigvalsh(mat(t))[0])
    root=brentq(low,1.05,1.12,xtol=1e-14);ev,V=np.linalg.eigh(mat(root));v=V[:,0];drive=-delta(root)@v
    rows=[];residual=mp.mpf(0)
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
            used=sorted(used);phis=[f.index(*b) for b in bonds]
            rhs=[mp.mpf(0)]*f.aug.n
            for coeff,(j,phase) in zip(drive,phis):
                rhs[f.em[j]]+=mp.mpc(float(coeff.real),float(coeff.imag))*conj(phase)
            solver=Refine(f.aug);sol=solver.solve(rhs)
            residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(sol),rhs)))
            w=f.dressed(sol[:f.n],sol[f.n:f.n+f.H.n])
            rows.append((f.ph,used,[w[f.index(*e)[0]] for e in used]))
            print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
            del solver,sol,w;gc.collect()
    cells=[[] for _ in range(3)]
    for cy in range(4*q):
        for cz in range(4*q):
            field={e:mp.mpc(0) for e in rows[0][1]}
            for ph,used,values in rows:
                for e,z in zip(used,values):
                    x,d=e;field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
            for d,b in enumerate(targets):cells[d].append(f.rawjet(b,field)[2])
    sums=[sum(c,mp.mpf(0)) for c in cells];maxima=[max(map(abs,c)) for c in cells]
    l1=[sum((abs(x) for x in c),mp.mpf(0)) for c in cells]
    ratios=[m/abs(s) for m,s in zip(maxima,sums)]
    previous=json.loads((OUT/'long_q2_R20_L2_second_coeffs.json').read_text())
    old=next(v for v in previous['variants'] if v['name']=='all_-1.0')
    comparison={'root_absolute_difference':abs(root-old['root']),
        'ratio_absolute_differences':[float(abs(r-mp.mpf(str(ro)))) for r,ro in zip(ratios,old['max_over_abs_sum'])],
        'sum_relative_differences':[float(abs((s-mp.mpf(str(o[0])))/s)) for s,o in zip(sums,old['first_physical_top_jet_sums'])]}
    result={'q':q,'R':R,'dps':dps,'candidate':'first segments +t, second segments -t',
        'crossing_drive':'double precision; root is not replayed or certified','root_double':root,
        'charged_low_double':list(map(float,ev[:4])),'boundary_null_norm_double':float(np.linalg.norm(mat(root)@v)),
        'first_physical_top_jet_sums':sums,'max_abs_first_top_jet':maxima,'l1_abs_first_top_jet':l1,
        'max_over_abs_sum':ratios,'abs_sum_over_l1':[abs(s)/a for s,a in zip(sums,l1)],
        'comparison_with_double_cached_columns':comparison,'flat_resolvent_absolute_residual':residual,
        'first_top_jet_cells':cells,'seconds':time.time()-start,
        'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'High-precision non-interval dressed solves from a double-precision Schur drive. Checks response and raw-cell stability only. No high-precision root, interval enclosure, Lean dictionary, P1/P2/KernelLine or cofinal proof.'}
    target=OUT/f'long_alternating_q2_R20_p{dps}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('RESULT',json.dumps(jsonable({k:v for k,v in result.items() if k!='first_top_jet_cells'}),indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=110);a=ap.parse_args();run(a.dps)
