#!/usr/bin/env python3
"""Numerical evidence only: signed-arm right stars on the original nine-bond Schur model.

The four arm angles are s_i*t, s_i in {-1,+1}.  Thus every variant has exactly
the same flat and pi-endpoint local carrier as rightStar.  The flat augmented
resolvent and all physical top-cell dressed solves are shared between variants.
No interval arithmetic, Lean identification, P1/P2 proof, or cofinality claim.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family,mp,np
import argparse,itertools,json,resource,time,gc,pickle
from scipy.optimize import brentq
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

# Order: (mu=1,outgoing), (mu=1,incoming), (mu=2,outgoing), (mu=2,incoming).
def geometry(boundary):
    lo=boundary;pls=[]
    for mu in [1,2]:
        for shift in [0,-1]:
            x=[lo-1,0,0];x[mu]=shift;x=tuple(x)
            inside=(lo,x[1],x[2]);xn=list(x);xn[mu]+=1;xn=tuple(xn)
            pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    active=[0,2,3]
    bonds=list(dict.fromkeys(p[i] for p in pls for i in active))
    return pls,bonds

def local(angles,charge=1):
    """Exact frozen four-edge local Hessian, transcribed from Family.plaq."""
    a0,a1,a2,a3=angles
    h=a0+a1-a2-a3
    co,si=np.cos(h),np.sin(h)
    cs=np.array([1,np.exp(2j*charge*a0),-np.exp(2j*charge*a3),-1])
    ans=co*np.outer(cs.conj(),cs)
    if charge:
        for r,s in itertools.combinations([2,3,0,1],2):
            v=-1j*si*cs[r].conjugate()*cs[s]
            ans[r,s]+=v;ans[s,r]+=v.conjugate()
    return ans

def embed_local(pls,bonds,angles_per_plaq,charge=1):
    ans=np.zeros((len(bonds),len(bonds)),complex)
    for p,angles in zip(pls,angles_per_plaq):
        m=local(angles,charge)
        for i in [0,2,3]:
            for j in [0,2,3]:
                ans[bonds.index(p[i]),bonds.index(p[j])]+=m[i,j]
    return ans

def run(q,R,selected,skip_jets=False,tag=None):
    start=time.time();mp.mp.dps=30
    boundary=q*(12*R+12);pls,bonds=geometry(boundary);n=len(bonds);nc=(4*q)**2
    C=np.zeros((n,n),complex);rows=[];residual=0.
    cache=OUT/f'flat_cache_q{q}_R{R}.pkl'
    if cache.exists():
        with cache.open('rb') as h:
            saved=pickle.load(h)
        C,rows,residual,targets=saved['C'],saved['rows'],saved['residual'],saved['targets']
        rows=[((r[0],r[1]),r[2],r[3]) if len(r)==4 else r for r in rows]
        f=Family(q,R,mp.mpf(0),0,0,1)
        print('LOADED',cache,flush=True)
    for iy in (range(4*q) if not cache.exists() else []):
        for iz in range(4*q):
            f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
            out,_=f.plaq('out',0)
            for i,row in enumerate(out.r):
                if i in f.em:
                    for j,v in row.items():
                        if j in f.em:f.aug.put(f.em[i],f.em[j],v)
            layer=f.s-2
            targets=[((layer,0,0),d) for d in range(3)]
            used=set()
            for b in targets:
                base,legs=f.rawdata[b];used.update(base)
                for l,m,r in legs:used.update(l+m+r)
            used=sorted(used);phis=[f.index(*b) for b in bonds]
            A=f.aug.scipy();rhs=np.zeros((A.shape[0],n),complex)
            ids=[f.em[j] for j,_ in phis];phases=np.array([complex(p) for _,p in phis])
            rhs[ids,range(n)]=phases.conjugate()
            from scipy.sparse.linalg import splu
            sol=splu(A).solve(rhs)
            residual=max(residual,float(np.max(np.abs(A@sol-rhs))))
            C+=phases[:,None]*sol[ids,:]/nc
            # dressed expects mp lists but double values work in its linear operations.
            cols=[]
            for col in range(n):
                w=f.dressed(list(sol[:f.n,col]),list(sol[f.n:f.n+f.H.n,col]))
                cols.append([w[f.index(*e)[0]] for e in used])
            rows.append((f.ph,used,cols))
            print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
            gc.collect()
    if not cache.exists():
        # Phases and columns are double-precision evidence data; caching only avoids
        # repeating the same flat solves while screening many local paths.
        cached_rows=[((complex(ph[0]),complex(ph[1])),used,np.asarray(cols,complex))
                     for ph,used,cols in rows]
        rows=cached_rows
        with cache.open('wb') as h:
            pickle.dump({'C':C,'rows':rows,'residual':residual,'targets':targets},h,protocol=5)
        print('WROTE',cache,flush=True)
    C=(C+C.conj().T)/2;S=np.linalg.inv(C)
    base=embed_local(pls,bonds,[[0,0,0,0]]*4)
    central=bonds.index(((boundary-1,0,0),0));leaves=[i for i in range(n) if i!=central]
    variants=[]
    for signs in selected:
        def delta(t,charge=1):
            return embed_local(pls,bonds,[[0,sign*t,0,0] for sign in signs],charge)-base
        def mat(t,charge=1):return S+delta(t,charge)
        def low(t):return float(np.linalg.eigvalsh(mat(t))[0])
        grid=np.linspace(0,np.pi,401);vals=list(map(low,grid))
        brackets=[(a,b) for a,b,fa,fb in zip(grid[:-1],grid[1:],vals[:-1],vals[1:]) if fa*fb<0]
        roots=[brentq(low,a,b,xtol=1e-14) for a,b in brackets]
        if not roots:
            variants.append({'signs':signs,'roots':roots,'halfpi_min':low(np.pi/2),'pi_min':low(np.pi),
                'status':'no sign-changing crossing'})
            continue
        root=roots[0];ev,V=np.linalg.eigh(mat(root));v=V[:,0]
        neutral_min=float(np.linalg.eigvalsh(mat(root,0))[0])
        restricted=[float(np.linalg.eigvalsh(mat(t)[np.ix_(leaves,leaves)])[0]) for t in [0,root,np.pi/2]]
        item={'signs':signs,'roots':roots,'root':root,'halfpi_min':low(np.pi/2),'pi_min':low(np.pi),
            'charged_low':list(map(float,ev[:4])),'neutral_min_at_crossing':neutral_min,
            'central_coordinate_abs':float(abs(v[central])),
            'central_zero_schur_min_at_0_root_halfpi':restricted,
            'status':'candidate' if 0<root<np.pi/2 and ev[1]>1e-7 and neutral_min>1e-7 and min(restricted)>1e-7 else 'rejected'}
        if not skip_jets:
            drive=-delta(root)@v
            compressed=[]
            for ph,used,cols in rows:
                compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
            cells=[[ ] for _ in range(3)]
            for cy in range(4*q):
                for cz in range(4*q):
                    field={e:0j for e in compressed[0][1]}
                    for ph,used,values in compressed:
                        for e,z in zip(used,values):
                            x,d=e
                            field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
                    for d,b in enumerate(targets):
                        cells[d].append(complex(f.rawjet(b,field)[2]))
            sums=[sum(c) for c in cells];maxima=[max(map(abs,c)) for c in cells]
            l1=[sum(map(abs,c)) for c in cells]
            item.update({'first_physical_top_jet_sums':sums,
                'max_abs_first_top_jet':maxima,'l1_abs_first_top_jet':l1,
                'max_over_abs_sum':[m/abs(s) if s else None for m,s in zip(maxima,sums)],
                'abs_sum_over_l1':[abs(s)/a if a else None for s,a in zip(sums,l1)],
                'first_top_jet_cells':cells})
        variants.append(item)
        print('VARIANT',signs,'root',root,'status',item['status'],
              'jets',item.get('first_physical_top_jet_sums'),flush=True)
    result={'q':q,'R':R,'boundary':boundary,'variants':variants,
        'flat_resolvent_absolute_residual':residual,'seconds':time.time()-start,
        'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'Double-precision, non-interval evidence only. Shared all-character full flat augmented resolvent; exact local Hessian algebra and Taylor jets. Schur spectra are not full-carrier spectra. Tiny jet values may be solver noise; no Lean dictionary or P1/P2/KernelLine/cofinal proof.'}
    if tag is None:
        tag='all' if len(selected)==16 else '_'.join(''.join('p' if s>0 else 'm' if s<0 else '0' for s in x) for x in selected)
    target=OUT/f'signed_q{q}_R{R}_{tag}.json'
    # Convert complex values to [real,imag] pairs for standard JSON.
    def clean(x):
        if isinstance(x,complex):return [x.real,x.imag]
        if isinstance(x,np.complex128):return [float(x.real),float(x.imag)]
        if isinstance(x,np.floating):return float(x)
        if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [clean(v) for v in x]
        return x
    target.write_text(json.dumps(clean(result),indent=2)+'\n')
    print('WROTE',target,flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,default=1);ap.add_argument('--R',type=int,default=20)
    ap.add_argument('--all-signs',action='store_true');ap.add_argument('--skip-jets',action='store_true')
    ap.add_argument('--signs',action='append',help='four +/- characters, e.g. +-+-; repeatable')
    ap.add_argument('--coeffs',action='append',help='four comma-separated real arm coefficients; repeatable')
    ap.add_argument('--tag',help='output filename tag')
    a=ap.parse_args()
    if a.all_signs:selected=list(itertools.product([-1,1],repeat=4))
    elif a.coeffs:selected=[tuple(float(c) for c in s.split(',')) for s in a.coeffs]
    elif a.signs:selected=[tuple(1 if c=='+' else -1 for c in s) for s in a.signs]
    else:selected=[(1,1,1,1),(1,-1,1,-1)]
    assert all(len(s)==4 for s in selected)
    run(a.q,a.R,selected,a.skip_jets,a.tag)
