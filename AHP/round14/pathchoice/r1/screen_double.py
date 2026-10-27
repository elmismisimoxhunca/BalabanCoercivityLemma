#!/usr/bin/env python3
"""Double-precision evidence for independent left/right exterior stars.

The full flat augmented resolvent is compressed to the union of the two
nine-bond boundary patches.  Local angles are cL*t on the left exterior
plaquette tangent and cR*t on the right one.  Controls cL=0 and cR=0 must
reproduce the retained one-sided stars.  No proof or interval claim.
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
import itertools,json,pickle,resource,time,gc
from scipy.optimize import brentq
from scipy.sparse.linalg import splu
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
OUT=Path(__file__).resolve().parent

def side_geometry(boundary,side):
    lo=boundary;pls=[]
    for mu in [1,2]:
        for shift in [0,-1]:
            x=[lo-1,0,0];x[mu]=shift;x=tuple(x)
            inside=(lo,x[1],x[2]);xn=list(x);xn[mu]+=1;xn=tuple(xn)
            pls.append([(x,0),(inside,mu),(xn,0),(x,mu)])
    active=[0,1,2] if side=='left' else [0,2,3]
    bonds=list(dict.fromkeys(p[i] for p in pls for i in active))
    return pls,bonds

def run(q,R,coefficients):
    start=time.time();mp.mp.dps=30;nc=(4*q)**2
    lp,lb=side_geometry(4*q,'left');rp,rb=side_geometry(q*(12*R+12),'right')
    bonds=lb+[b for b in rb if b not in lb];n=len(bonds)
    cache=OUT/f'double_flat_q{q}_R{R}.pkl'
    if cache.exists():
        with cache.open('rb') as h:saved=pickle.load(h)
        C,rows,residual,targets=saved['C'],saved['rows'],saved['residual'],saved['targets']
        rows=[((r[0],r[1]),r[2],r[3]) if len(r)==4 else r for r in rows]
        f=Family(q,R,mp.mpf(0),0,0,1);print('LOADED',cache,flush=True)
    else:
        C=np.zeros((n,n),complex);rows=[];residual=0.
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
                A=f.aug.scipy();rhs=np.zeros((A.shape[0],n),complex)
                ids=[f.em[j] for j,_ in phis];phases=np.array([complex(p) for _,p in phis])
                rhs[ids,range(n)]=phases.conjugate();sol=splu(A).solve(rhs)
                residual=max(residual,float(np.max(np.abs(A@sol-rhs))))
                C+=phases[:,None]*sol[ids,:]/nc;cols=[]
                for col in range(n):
                    w=f.dressed(list(sol[:f.n,col]),list(sol[f.n:f.n+f.H.n,col]))
                    cols.append([w[f.index(*e)[0]] for e in used])
                rows.append(((complex(f.ph[0]),complex(f.ph[1])),used,np.asarray(cols,complex)))
                print('SECTOR',iy,iz,'seconds',round(time.time()-start,2),flush=True);gc.collect()
        with cache.open('wb') as h:pickle.dump({'C':C,'rows':rows,'residual':residual,'targets':targets},h,protocol=5)
        print('WROTE',cache,flush=True)
    C=(C+C.conj().T)/2;S=np.linalg.inv(C)
    def patch(cL,cR,t,charge=1):
        ans=np.zeros((n,n),complex)
        for side,pls,c in [('left',lp,cL),('right',rp,cR)]:
            active=[0,1,2] if side=='left' else [0,2,3]
            for p in pls:
                angles=[0,0,0,c*t] if side=='left' else [0,c*t,0,0]
                m=local(angles,charge)
                for i in active:
                    for j in active:ans[bonds.index(p[i]),bonds.index(p[j])]+=m[i,j]
        return ans
    base=patch(0,0,0)
    def delta(cL,cR,t,charge=1):return patch(cL,cR,t,charge)-base
    centralL=bonds.index(((4*q-1,0,0),0));centralR=bonds.index(((q*(12*R+12)-1,0,0),0))
    leavesL=[i for i in range(n) if i!=centralL];leavesR=[i for i in range(n) if i!=centralR]
    leavesBoth=[i for i in range(n) if i not in [centralL,centralR]]
    reports=[]
    for cL,cR in coefficients:
        def mat(t,charge=1):return S+delta(cL,cR,t,charge)
        def low(t):return float(np.linalg.eigvalsh(mat(t))[0])
        grid=np.linspace(0,np.pi,301);values=list(map(low,grid))
        roots=[brentq(low,a,b,xtol=1e-13) for a,b,fa,fb in
               zip(grid[:-1],grid[1:],values[:-1],values[1:]) if fa*fb<0]
        item={'cL':cL,'cR':cR,'roots':roots,'halfpi_min':low(np.pi/2),'pi_min':low(np.pi)}
        if not roots:item['status']='no sign-changing crossing';reports.append(item);continue
        root=roots[0];ev,V=np.linalg.eigh(mat(root));v=V[:,0]
        neutral=float(np.linalg.eigvalsh(mat(root,0))[0])
        restricted={name:[float(np.linalg.eigvalsh(mat(t)[np.ix_(ids,ids)])[0]) for t in [0,root,np.pi/2]]
                    for name,ids in [('left',leavesL),('right',leavesR),('both',leavesBoth)]}
        item.update({'root':root,'charged_low':list(map(float,ev[:5])),'neutral_min_at_crossing':neutral,
            'central_abs_left':float(abs(v[centralL])),'central_abs_right':float(abs(v[centralR])),
            'central_zero_schur_min':restricted,
            'status':'candidate' if 0<root<np.pi/2 and ev[1]>1e-6 and neutral>1e-7 and min(restricted['both'])>1e-7 else 'rejected'})
        drive=-delta(cL,cR,root)@v;compressed=[]
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
            'abs_sum_over_l1':[abs(s)/a if a else None for s,a in zip(sums,l1)],'first_top_jet_cells':cells})
        reports.append(item);print('VARIANT',cL,cR,'root',root,item['status'],'ratios',item['max_over_abs_sum'],
            'gap',ev[1],'jets',sums,flush=True)
    result={'q':q,'R':R,'flat_resolvent_absolute_residual':residual,'variants':reports,
        'seconds':time.time()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'qualification':'Double-precision non-interval evidence only. Full all-character flat augmented resolvent on the union of left/right boundary patches. Central-zero rows are numerical diagnostics, not a proved P2 for a double star. No Lean dictionary, kernel-line, or cofinal claim.'}
    def clean(x):
        if isinstance(x,(complex,np.complex128)):return [float(x.real),float(x.imag)]
        if isinstance(x,np.floating):return float(x)
        if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
        if isinstance(x,(list,tuple)):return [clean(v) for v in x]
        return x
    target=OUT/f'double_q{q}_R{R}.json';target.write_text(json.dumps(clean(result),indent=2)+'\n')
    print('WROTE',target,flush=True)

if __name__=='__main__':
    vals=[-3.,-2.,-1.,-.5,-.25,0.,.25,.5,1.,2.,3.]
    cs=[]
    for c in vals:
        cs.extend([(c,1.),(1.,c),(c,-1.),(-1.,c)])
    cs.extend([(0.,0.),(0.,1.),(1.,0.)]);cs=list(dict.fromkeys(cs))
    run(2,20,cs)
