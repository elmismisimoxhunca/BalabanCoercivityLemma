#!/usr/bin/env python3
"""Double-precision evidence for two right stars at transverse positions.

Every path bond is transverse and has both endpoints outside Omega0, hence is
in the frozen Zb support.  The full all-character flat augmented resolvent is
compressed to the union of the two physical nine-bond patches.  Local Hessians
and Taylor raw jets are the same formulas as the round-1 controls.  This is
non-interval numerical evidence only, not a P1/P2/KernelLine or P3 proof.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
sys.path.insert(0,str(ROOT/'AHP/round14/pathchoice/r1'))
from probe import Family,mp,np
from screen_signed import geometry,local
import argparse,itertools,json,pickle,resource,time,gc
from scipy.optimize import brentq
from scipy.sparse.linalg import splu
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def shift_plaquette(p,sy,sz):
    ans=[]
    for (x,y,z),d in p:
        ans.append(((x,y+sy,z+sz),d))
    return ans

def cluster_geometry(boundary,centers):
    pls=[]
    for sy,sz in centers:
        pls.extend(shift_plaquette(p,sy,sz) for p in geometry(boundary)[0])
    active=[0,2,3]
    bonds=list(dict.fromkeys(p[i] for p in pls for i in active))
    return pls,bonds

def patch(pls,bonds,coefficients,t,charge=1):
    ans=np.zeros((len(bonds),len(bonds)),complex)
    assert len(coefficients)*4==len(pls)
    for k,p in enumerate(pls):
        c=coefficients[k//4]
        m=local([0,c*t,0,0],charge)
        for i in [0,2,3]:
            for j in [0,2,3]:
                ans[bonds.index(p[i]),bonds.index(p[j])]+=m[i,j]
    return ans

def run(q,R,centers,variants,tag):
    start=time.time(); mp.mp.dps=30; nc=(4*q)**2
    boundary=q*(12*R+12); pls,bonds=cluster_geometry(boundary,centers); n=len(bonds)
    center_tag='_'.join(f'{sy}x{sz}' for sy,sz in centers)
    cache=OUT/f'cluster_flat_q{q}_R{R}_{center_tag}.pkl'
    if cache.exists():
        with cache.open('rb') as h: saved=pickle.load(h)
        C,rows,residual,targets=saved['C'],saved['rows'],saved['residual'],saved['targets']
        rows=[((r[0],r[1]),r[2],r[3]) if len(r)==4 else r for r in rows]
        f=Family(q,R,mp.mpf(0),0,0,1)
        print('LOADED',cache,'dimension',n,flush=True)
    else:
        C=np.zeros((n,n),complex); rows=[]; residual=0.
        for iy in range(4*q):
            for iz in range(4*q):
                f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
                out,_=f.plaq('out',0)
                for i,row in enumerate(out.r):
                    if i in f.em:
                        for j,v in row.items():
                            if j in f.em: f.aug.put(f.em[i],f.em[j],v)
                targets=[((f.s-2,0,0),d) for d in range(3)]
                used=set()
                for b in targets:
                    base,legs=f.rawdata[b]; used.update(base)
                    for l,m,r in legs: used.update(l+m+r)
                used=sorted(used); phis=[f.index(*b) for b in bonds]
                A=f.aug.scipy(); rhs=np.zeros((A.shape[0],n),complex)
                ids=[f.em[j] for j,_ in phis]; phases=np.array([complex(p) for _,p in phis])
                rhs[ids,range(n)]=phases.conjugate(); sol=splu(A).solve(rhs)
                residual=max(residual,float(np.max(np.abs(A@sol-rhs))))
                C+=phases[:,None]*sol[ids,:]/nc; cols=[]
                for col in range(n):
                    w=f.dressed(list(sol[:f.n,col]),list(sol[f.n:f.n+f.H.n,col]))
                    cols.append([w[f.index(*e)[0]] for e in used])
                rows.append(((complex(f.ph[0]),complex(f.ph[1])),used,np.asarray(cols,complex)))
                print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
                gc.collect()
        with cache.open('wb') as h:
            pickle.dump({'C':C,'rows':rows,'residual':residual,'targets':targets},h,protocol=5)
        print('WROTE',cache,flush=True)
    C=(C+C.conj().T)/2; S=np.linalg.inv(C)
    base=patch(pls,bonds,[0]*len(centers),0)
    central=[]
    for sy,sz in centers:
        central.append(bonds.index(((boundary-1,sy,sz),0)))
    reports=[]
    for name,coefficients in variants:
        def delta(t,charge=1): return patch(pls,bonds,coefficients,t,charge)-base
        def mat(t,charge=1): return S+delta(t,charge)
        def low(t): return float(np.linalg.eigvalsh(mat(t))[0])
        grid=np.linspace(0,np.pi,321); values=list(map(low,grid))
        roots=[brentq(low,a,b,xtol=1e-13) for a,b,fa,fb in
               zip(grid[:-1],grid[1:],values[:-1],values[1:]) if fa*fb<0]
        item={'name':name,'centers':centers,'coefficients':coefficients,
              'path_bonds':[[list(b[0]),b[1]] for b in bonds],
              'roots':roots,'halfpi_min':low(np.pi/2),'pi_min':low(np.pi)}
        if not roots:
            item['status']='no sign-changing crossing'; reports.append(item); continue
        root=roots[0]; ev,V=np.linalg.eigh(mat(root)); v=V[:,0]
        neutral=float(np.linalg.eigvalsh(mat(root,0))[0])
        restricted={}
        for label,excluded in [('A',[central[0]]),('B',[central[1]]),('both',central)]:
            ids=[i for i in range(n) if i not in excluded]
            restricted[label]=[float(np.linalg.eigvalsh(mat(t)[np.ix_(ids,ids)])[0])
                               for t in [0,root,np.pi/2]]
        item.update({'root':root,'charged_low':list(map(float,ev[:6])),
            'neutral_min_at_crossing':neutral,
            'central_coordinate_abs':[float(abs(v[i])) for i in central],
            'central_zero_schur_min':restricted,
            'status':'candidate' if 0<root<np.pi/2 and ev[1]>1e-7 and neutral>1e-7
                     and min(restricted['both'])>1e-7 else 'rejected'})
        drive=-delta(root)@v; compressed=[]
        for ph,used,cols in rows:
            compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n))
                                        for i in range(len(used))]))
        cells=[[] for _ in range(3)]
        for cy in range(4*q):
            for cz in range(4*q):
                field={e:0j for e in compressed[0][1]}
                for ph,used,values in compressed:
                    for e,z in zip(used,values):
                        x,d=e
                        field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
                for d,b in enumerate(targets): cells[d].append(complex(f.rawjet(b,field)[2]))
        sums=[sum(c) for c in cells]; maxima=[max(map(abs,c)) for c in cells]
        l1=[sum(map(abs,c)) for c in cells]
        common_sign=[]
        for c,s in zip(cells,sums):
            common_sign.append(all((x.real*s.real>=-1e-14*abs(s) if abs(s.real)>abs(s.imag)
                                    else x.imag*s.imag>=-1e-14*abs(s)) for x in c))
        item.update({'first_physical_top_jet_sums':sums,'max_abs_first_top_jet':maxima,
            'l1_abs_first_top_jet':l1,
            'max_over_abs_sum':[m/abs(s) if s else None for m,s in zip(maxima,sums)],
            'abs_sum_over_l1':[abs(s)/a if a else None for s,a in zip(sums,l1)],
            'common_sign_diagnostic':common_sign,'first_top_jet_cells':cells})
        reports.append(item)
        print('VARIANT',name,'root',root,item['status'],'ratios',item['max_over_abs_sum'],
              'gap',ev[1],'jets',sums,flush=True)
    result={'q':q,'R':R,'centers':centers,'boundary':boundary,
        'flat_resolvent_absolute_residual':residual,'variants':reports,
        'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'Double-precision non-interval evidence only. Full all-character flat augmented resolvent on the union of two right boundary patches. Exact local Hessian and Taylor jet formulas. Central-zero rows are numerical diagnostics, not P2. No spectral enclosure, Lean dictionary, KernelLine, or cofinal claim.'}
    def clean(x):
        if isinstance(x,(complex,np.complex128)): return [float(x.real),float(x.imag)]
        if isinstance(x,np.floating): return float(x)
        if isinstance(x,dict): return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)): return [clean(v) for v in x]
        return x
    target=OUT/f'cluster_q{q}_R{R}_{tag}.json'
    target.write_text(json.dumps(clean(result),indent=2)+'\n')
    print('WROTE',target,flush=True)

def default_variants():
    ans=[]
    def add(a,b,name=None):
        if name is None: name=f'A{a}_B{b}'
        ans.append((name,[float(a),float(b)]))
    add(1,0,'original_only'); add(0,1,'translated_only'); add(1,1,'equal')
    vals=[-3.,-2.,-1.,-.5,-.25,.25,.5,1.,2.,3.]
    for c in vals:
        add(1,c); add(c,1); add(1,-c,f'A1_B{-c}'); add(-c,1,f'A{-c}_B1')
    for a,b in [(0.1,1),(0.2,1),(0.5,2),(2,.5),(4,1),(1,4),(-2,2),(2,-2),
                (3,-1),(-1,3),(2,2),(-2,-2),(0.5,-2),(-2,.5)]:
        add(a,b)
    seen=set(); out=[]
    for name,c in ans:
        key=tuple(c)
        if key not in seen:
            seen.add(key); out.append((name,c))
    return out

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--q',type=int,default=2)
    ap.add_argument('--R',type=int,default=20); ap.add_argument('--centers',default='0,0;2,0')
    ap.add_argument('--tag',default='2x0')
    a=ap.parse_args()
    centers=[tuple(map(int,s.split(','))) for s in a.centers.split(';')]
    assert len(centers)==2
    run(a.q,a.R,centers,default_variants(),a.tag)
