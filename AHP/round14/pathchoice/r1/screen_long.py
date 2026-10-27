#!/usr/bin/env python3
"""Double-precision evidence for right stars with longer exterior transverse arms.

A path bond (mu,y,z) is ((lo,y,z),mu), with both endpoints outside Omega0.
Each contributes its genuine mixed interior/exterior plaquette.  The active
Schur variables are exactly the other three edges of all such plaquettes.
The flat full augmented resolvent is shared by every variant on a fixed
length-two patch.  No interval certificate or Lean claim is made.
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
from screen_signed import local
import argparse,itertools,json,pickle,resource,time,gc
from scipy.optimize import brentq
from scipy.sparse.linalg import splu
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def axial(mu,k):
    return (mu,k,0) if mu==1 else (mu,0,k)

def geometry(boundary,path_bonds):
    lo=boundary;pls=[]
    for mu,y,z in path_bonds:
        x=(lo-1,y,z);inside=(lo,y,z)
        xn=list(x);xn[mu]+=1;xn=tuple(xn)
        pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    bonds=list(dict.fromkeys(p[i] for p in pls for i in [0,2,3]))
    return pls,bonds

def embed(pls,bonds,coefficients,t,charge=1):
    ans=np.zeros((len(bonds),len(bonds)),complex)
    for p,c in zip(pls,coefficients):
        m=local([0,c*t,0,0],charge)
        for i in [0,2,3]:
            for j in [0,2,3]:ans[bonds.index(p[i]),bonds.index(p[j])]+=m[i,j]
    return ans

def run(q,R,variants,tag,length=2):
    start=time.time();mp.mp.dps=30;lo=q*(12*R+12)
    # For each mu, k=-1,0 are the original arms; the full interval also
    # includes negative extensions k<-1 and positive extensions k>0.
    path_bonds=[axial(mu,k) for mu in [1,2] for k in range(-length,length)]
    pls,bonds=geometry(lo,path_bonds);n=len(bonds);nc=(4*q)**2
    cache=OUT/f'long_flat_q{q}_R{R}_L{length}_axial.pkl'
    if cache.exists():
        with cache.open('rb') as h:saved=pickle.load(h)
        C,rows,residual,targets=saved['C'],saved['rows'],saved['residual'],saved['targets']
        rows=[((r[0],r[1]),r[2],r[3]) if len(r)==4 else r for r in rows]
        f=Family(q,R,mp.mpf(0),0,0,1)
        print('LOADED',cache,'dimension',n,flush=True)
    else:
        C=np.zeros((n,n),complex);rows=[];residual=0.
        for iy in range(4*q):
            for iz in range(4*q):
                f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
                out,_=f.plaq('out',0)
                for i,row in enumerate(out.r):
                    if i in f.em:
                        for j,v in row.items():
                            if j in f.em:f.aug.put(f.em[i],f.em[j],v)
                targets=[((f.s-2,0,0),d) for d in range(3)]
                used=set()
                for b in targets:
                    base,legs=f.rawdata[b];used.update(base)
                    for l,m,r in legs:used.update(l+m+r)
                used=sorted(used);phis=[f.index(*b) for b in bonds]
                A=f.aug.scipy();rhs=np.zeros((A.shape[0],n),complex)
                ids=[f.em[j] for j,_ in phis];phases=np.array([complex(p) for _,p in phis])
                rhs[ids,range(n)]=phases.conjugate();sol=splu(A).solve(rhs)
                residual=max(residual,float(np.max(np.abs(A@sol-rhs))))
                C+=phases[:,None]*sol[ids,:]/nc;cols=[]
                for col in range(n):
                    w=f.dressed(list(sol[:f.n,col]),list(sol[f.n:f.n+f.H.n,col]))
                    cols.append([w[f.index(*e)[0]] for e in used])
                rows.append(((complex(f.ph[0]),complex(f.ph[1])),used,np.asarray(cols,complex)))
                print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True)
                gc.collect()
        with cache.open('wb') as h:
            pickle.dump({'C':C,'rows':rows,'residual':residual,'targets':targets},h,protocol=5)
        print('WROTE',cache,flush=True)
    C=(C+C.conj().T)/2;S=np.linalg.inv(C);base=embed(pls,bonds,[0]*len(path_bonds),0)
    # base above is flat because t=0; all coefficients are irrelevant there.
    central=bonds.index(((lo-1,0,0),0));leaves=[i for i in range(n) if i!=central]
    reports=[]
    for name,cmap in variants:
        coefficients=[float(cmap.get(b,0)) for b in path_bonds]
        def delta(t,charge=1):return embed(pls,bonds,coefficients,t,charge)-base
        def mat(t,charge=1):return S+delta(t,charge)
        def low(t):return float(np.linalg.eigvalsh(mat(t))[0])
        grid=np.linspace(0,np.pi,401);values=list(map(low,grid))
        roots=[brentq(low,a,b,xtol=1e-14) for a,b,fa,fb in
               zip(grid[:-1],grid[1:],values[:-1],values[1:]) if fa*fb<0]
        item={'name':name,'coefficients':dict((str(k),v) for k,v in cmap.items()),
              'path_bonds':path_bonds,'roots':roots,'halfpi_min':low(np.pi/2),'pi_min':low(np.pi)}
        if not roots:
            item['status']='no sign-changing crossing';reports.append(item);continue
        root=roots[0];ev,V=np.linalg.eigh(mat(root));v=V[:,0]
        neutral=float(np.linalg.eigvalsh(mat(root,0))[0])
        restricted=[float(np.linalg.eigvalsh(mat(t)[np.ix_(leaves,leaves)])[0]) for t in [0,root,np.pi/2]]
        item.update({'root':root,'charged_low':list(map(float,ev[:4])),'neutral_min_at_crossing':neutral,
            'central_coordinate_abs':float(abs(v[central])),
            'central_zero_schur_min_at_0_root_halfpi':restricted,
            'status':'candidate' if 0<root<np.pi/2 and ev[1]>1e-7 and neutral>1e-7 and min(restricted)>1e-7 else 'rejected'})
        drive=-delta(root)@v;compressed=[]
        for ph,used,cols in rows:
            compressed.append((ph,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
        cells=[[] for _ in range(3)]
        for cy in range(4*q):
            for cz in range(4*q):
                field={e:0j for e in compressed[0][1]}
                for ph,used,values in compressed:
                    for e,z in zip(used,values):
                        x,d=e;field[e]+=ph[0]**(x[1]//2+cy)*ph[1]**(x[2]//2+cz)*z/nc
                for d,b in enumerate(targets):cells[d].append(complex(f.rawjet(b,field)[2]))
        sums=[sum(c) for c in cells];maxima=[max(map(abs,c)) for c in cells];l1=[sum(map(abs,c)) for c in cells]
        item.update({'first_physical_top_jet_sums':sums,'max_abs_first_top_jet':maxima,
            'l1_abs_first_top_jet':l1,'max_over_abs_sum':[m/abs(s) if s else None for m,s in zip(maxima,sums)],
            'abs_sum_over_l1':[abs(s)/a if a else None for s,a in zip(sums,l1)],
            'first_top_jet_cells':cells})
        reports.append(item)
        print('VARIANT',name,'root',root,item['status'],'ratios',item['max_over_abs_sum'],
              'jets',item['first_physical_top_jet_sums'],flush=True)
    result={'q':q,'R':R,'length':length,'boundary':lo,'flat_resolvent_absolute_residual':residual,
        'variants':reports,'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'Double-precision non-interval evidence only. All-character full flat augmented solve on an enlarged physical boundary patch; exact local Hessian and Taylor jets. Not a Lean dictionary, spectral enclosure, P1/P2/KernelLine proof, or cofinal result.'}
    def clean(x):
        if isinstance(x,(complex,np.complex128)):return [float(x.real),float(x.imag)]
        if isinstance(x,np.floating):return float(x)
        if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [clean(v) for v in x]
        return x
    target=OUT/f'long_q{q}_R{R}_L{length}_{tag}.json';target.write_text(json.dumps(clean(result),indent=2)+'\n')
    print('WROTE',target,flush=True)

def original():
    return {(1,0,0):1,(1,-1,0):1,(2,0,0):1,(2,0,-1):1}

def extension_variants():
    ans=[('original',original())];orig=original()
    extensions=[axial(1,1),axial(1,-2),axial(2,1),axial(2,-2)]
    for mask in range(1,16):
        c=dict(orig);names=[]
        for i,b in enumerate(extensions):
            if mask>>i&1:c[b]=1;names.append(str(b))
        ans.append(('extend_'+'_'.join(names),c))
    for c in [-2.,-1.,-.5,.5,2.]:
        d=dict(orig)
        for b in extensions:d[b]=c
        ans.append(('all_second_'+str(c),d))
    return ans

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,default=2);ap.add_argument('--R',type=int,default=20)
    ap.add_argument('--length',type=int,default=2);ap.add_argument('--tag',default='extensions')
    a=ap.parse_args();run(a.q,a.R,extension_variants(),a.tag,a.length)
