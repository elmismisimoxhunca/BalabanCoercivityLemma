#!/usr/bin/env python3
"""High-precision dressed-solve replay of the low-cancellation L3 candidate.

The Schur drive is double precision, as in round 1.  Every augmented dressed
solve, residual, reconstruction and raw jet uses mpmath.  All physical rows
are evaluated in direction 1 using blockBase=p+2*j.  This checks numerical
response/sign structure only; it is not a root enclosure or a Lean proof.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
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

def coefficients(c2,c3):
    cmap=original()
    for b in [axial(1,1),axial(1,-2),axial(2,1),axial(2,-2)]: cmap[b]=c2
    for b in [axial(1,2),axial(1,-3),axial(2,2),axial(2,-3)]: cmap[b]=c3
    return cmap

def run(q,R,dps,c2,c3):
    mp.mp.dps=dps; start=time.time(); nc=(4*q)**2; length=3
    lo=q*(12*R+12); path_bonds=[axial(mu,k) for mu in [1,2] for k in range(-length,length)]
    pls,bonds=geometry(lo,path_bonds); n=len(bonds)
    cache=OUT/f'long_flat_q{q}_R{R}_L3_axial.pkl'
    if not cache.exists(): raise FileNotFoundError(f'build the double cache first: {cache}')
    with cache.open('rb') as h: saved=pickle.load(h)
    C=saved['C']; C=(C+C.conj().T)/2; S=np.linalg.inv(C)
    cmap=coefficients(c2,c3); coeffs=[float(cmap.get(b,0)) for b in path_bonds]
    base=embed(pls,bonds,coeffs,0)
    def delta(t,charge=1): return embed(pls,bonds,coeffs,t,charge)-base
    def mat(t,charge=1): return S+delta(t,charge)
    def low(t): return float(np.linalg.eigvalsh(mat(t))[0])
    grid=np.linspace(.8,1.4,121); vals=list(map(low,grid))
    brackets=[(a,b) for a,b,fa,fb in zip(grid[:-1],grid[1:],vals[:-1],vals[1:]) if fa*fb<0]
    if not brackets: raise RuntimeError('no crossing bracket in .8,1.4')
    root=brentq(low,*brackets[0],xtol=1e-14)
    ev,V=np.linalg.eigh(mat(root)); v=V[:,0]; drive=-delta(root)@v
    central=bonds.index(((lo-1,0,0),0)); leaves=[i for i in range(n) if i!=central]
    restricted=[float(np.linalg.eigvalsh(mat(t)[np.ix_(leaves,leaves)])[0]) for t in [0,root,np.pi/2]]
    neutral=float(np.linalg.eigvalsh(mat(root,0))[0])
    rows=[]; residual=mp.mpf(0)
    for iy in range(4*q):
        for iz in range(4*q):
            f=Family(q,R,mp.mpf(0),iy,iz,1).assemble(); out,_=f.plaq('out',0)
            for i,row in enumerate(out.r):
                if i in f.em:
                    for j,val in row.items():
                        if j in f.em: f.aug.put(f.em[i],f.em[j],val)
            phis=[f.index(*b) for b in bonds]
            rhs=[mp.mpf(0)]*f.aug.n
            for coeff,(j,phase) in zip(drive,phis):
                rhs[f.em[j]]+=mp.mpc(float(coeff.real),float(coeff.imag))*conj(phase)
            solver=Refine(f.aug); sol=solver.solve(rhs)
            residual=max(residual,max(abs(a-b) for a,b in zip(f.aug.apply(sol),rhs)))
            w=f.dressed(sol[:f.n],sol[f.n:f.n+f.H.n])
            rows.append((f.ph,w))
            print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
            del solver,sol,w; gc.collect()
    block_count=4*q*(R+1); last=block_count-1
    reports=[]
    for j in range(block_count):
        layer=f.p+2*j; target=((layer,0,0),1)
        base_target,legs=f.rawdata[target]; used=set(base_target)
        for l,m,r in legs: used.update(l+m+r)
        used=sorted(used)
        compressed=[]
        for ph,w in rows:
            compressed.append((ph,[w[f.index(*e)[0]] for e in used]))
        cells=[]
        for cy in range(4*q):
            for cz in range(4*q):
                field={e:mp.mpc(0) for e in used}
                for ph,values in compressed:
                    for e,z in zip(used,values):
                        x,d=e
                        field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
                cells.append(f.rawjet(target,field)[2])
        total=sum(cells,mp.mpf(0)); maximum=max(map(abs,cells)); l1=sum((abs(z) for z in cells),mp.mpf(0))
        neg=[(i,z) for i,z in enumerate(cells) if z<0]; pos=[(i,z) for i,z in enumerate(cells) if z>0]
        reports.append({'j':j,'layer':layer,'sum':total,'max_abs_cell':maximum,'l1_abs_cells':l1,
            'max_over_abs_sum':maximum/abs(total) if total else None,
            'abs_sum_over_l1':abs(total)/l1 if l1 else None,
            'negative_count':len(neg),'positive_count':len(pos),'zero_count':len(cells)-len(neg)-len(pos),
            'common_weak_sign':not neg or not pos,
            'sign_exceptions':[{'cell_linear_index':i,'value':z} for i,z in (neg if len(neg)<len(pos) else pos)],
            'cells_if_last_row':cells if j==last else None})
        if j%12==0 or j==last: print('ROW',j,'seconds',round(time.time()-start,2),flush=True)
    candidate=json.loads((OUT/f'long_q{q}_R{R}_L3_L3_targeted.json').read_text()) if q==2 and R==20 else None
    old=None
    if candidate:
        name=f'c2_{c2:.12g}_c3_{c3:.12g}'
        old=next(v for v in candidate['variants'] if v['name']==name)
    right=reports[-1]
    common=[r['j'] for r in reports if r['common_weak_sign'] and r['sum']!=0]
    best_ratio=min(reports,key=lambda r:r['max_over_abs_sum'] if r['max_over_abs_sum'] is not None else mp.inf)
    best_l1=max(reports,key=lambda r:r['abs_sum_over_l1'] if r['abs_sum_over_l1'] is not None else -1)
    comparison=None
    if old:
        comparison={'root_absolute_difference':abs(root-old['root']),
            'right_row_ratio_absolute_difference':abs(right['max_over_abs_sum']-mp.mpf(str(old['max_over_abs_sum'][1]))),
            'right_row_sum_relative_difference':abs((right['sum']-mp.mpf(str(old['first_physical_top_jet_sums'][1][0])))/right['sum'])}
    result={'q':q,'R':R,'dps':dps,'second_segment_coefficient':c2,'third_segment_coefficient':c3,
        'crossing_drive':'double precision; root and spectral values are not high-precision enclosures',
        'root_double':root,'charged_low_double':list(map(float,ev[:5])),
        'neutral_min_double':neutral,'central_zero_schur_min_double':restricted,
        'boundary_null_norm_double':float(np.linalg.norm(mat(root)@v)),
        'flat_resolvent_absolute_residual':residual,'block_count':block_count,'right_row_j':last,
        'right_row':right,'rows':reports,'common_weak_sign_rows':common,
        'best_ratio_row_j':best_ratio['j'],'best_l1_row_j':best_l1['j'],
        'comparison_with_double_cached_columns':comparison,'seconds':time.time()-start,
        'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'High-precision non-interval dressed solves from a double-precision Schur drive. All physical rows use the exact blockBase progression and Taylor raw jets. No high-precision root, interval certificate, P1/P2/KernelLine or P3 proof.'}
    tag=f'tail_q{q}_R{R}_c2_{c2:.12g}_c3_{c3:.12g}_p{dps}'.replace('-','m').replace('.','_')
    target=OUT/f'{tag}.json'; target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('SUMMARY',json.dumps(jsonable({k:v for k,v in result.items() if k not in ['rows','right_row']}),indent=2),flush=True)
    print('RIGHT_ROW',json.dumps(jsonable({k:v for k,v in right.items() if k!='cells_if_last_row'}),indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--q',type=int,default=2); ap.add_argument('--R',type=int,default=20)
    ap.add_argument('--dps',type=int,default=110); ap.add_argument('--c2',type=float,default=-.25)
    ap.add_argument('--c3',type=float,default=-2.25); a=ap.parse_args()
    run(a.q,a.R,a.dps,a.c2,a.c3)
