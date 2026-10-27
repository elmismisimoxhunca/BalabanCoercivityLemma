#!/usr/bin/env python3
"""Initial-positivity diagnostics and sector scan. Operators: SOURCES.md.
mp LDL gives numerical inertia, not interval-certified inertia. Double
ARPACK supplies optional gap diagnostics and is labelled separately.
"""
import sys
sys.dont_write_bytecode = True
from probe import *
from scipy.sparse.linalg import eigsh, LinearOperator

def poly_raw(f,b):
    """All charged directions at once. a2=z* C z, b1=row*z.
    Exact quadratic coefficient algebra in mpmath; no finite differences.
    """
    base,legs=f.rawdata[b];used=set(base)
    for l,m,r in legs:used.update(l+m+r)
    used=sorted(used);n=len(used);ix={e:i for i,e in enumerate(used)}
    zv=np.zeros(n,dtype=object);zm=np.zeros((n,n),dtype=object)
    def cj(a):return np.conjugate(a)
    def outer(a,b):return cj(a)[:,None]*b[None,:]
    def H(a):return cj(a.T)
    def mul(g,h):
        a,b,c=g;d,e,ff=h
        return a*d,a*e+b*conj(d),a*ff+c*d-outer(e,b)
    def dag(g):return conj(g[0]),-g[1],H(g[2])
    def ex(v):
        s,z,c=v
        if not s:return 1,z,1j*c-outer(z,z)/2
        si=mp.sin(s);co=mp.cos(s)
        return mp.mpc(co,si),si/s*z,(-si+1j*co)*c+(-si/(2*s)+1j*(s*co-si)/(2*s*s))*outer(z,z)
    def lg(g):
        a,b,c=g;s=mp.arg(a);im=(c-H(c))/(2j)
        if not s:return 0,b,im
        si=mp.sin(s);co=mp.cos(s)
        return s,s/si*b,s/si*im+(s*co-si)/(si*si)*(c+H(c))/2
    def addj(a,b):return tuple(x+y for x,y in zip(a,b))
    def scale(a,c):return tuple(c*x for x in a)
    one=(1,zv,zm);zero=(0,zv,zm)
    @lru_cache(None)
    def link(e):
        u=mp.exp(1j*f.angle(e));v=zv.copy();v[ix[e]]=conj(u)
        C=zm.copy();C[ix[e],ix[e]]=-u/2
        return u,v,C
    def hol(path):
        a=one
        for e in path:a=mul(a,link(e))
        return a
    def bg(path):return mp.exp(1j*sum(f.angle(e) for e in path)),zv,zm
    B=hol(base);S=zero;sm=zero;sp=zero
    for l,m,r in legs:
        L=hol(l);rr=hol(r)
        S=addj(S,scale(lg(mul(mul(mul(L,hol(m)),dag(rr)),dag(B))),mp.mpf(1)/8))
        sm=addj(sm,scale(lg(mul(L,dag(bg(l)))),mp.mpf(1)/8))
        sp=addj(sp,scale(lg(mul(rr,dag(bg(r)))),mp.mpf(1)/8))
    blocked=mul(ex(S),B)
    background=mp.exp(1j*(S[0]+sum(f.angle(e) for e in base)))
    word=mul(mul(mul(ex(scale(sm,-1)),blocked),ex(sp)),(conj(background),zv,zm))
    return used,lg(word)[2]/2

POLY_CACHE={}
def draw(f,hj):
    D=Sp(len(f.bonds),len(f.bonds));cache=POLY_CACHE;checks=[]
    for b,h in zip(f.b1,hj):
        if not h:continue
        x,d=b;base,legs=f.rawdata[b];used=set(base)
        for l,m,r in legs:used.update(l+m+r)
        used=sorted(used)
        key=(mp.mp.dps,d,tuple(f.angle(e) for e in used))
        if key not in cache:
            _,C=poly_raw(f,b);cache[key]=C
            # Independent directional check of full local Hessian.
            z=[mp.mpc((i%5)-2,(i%7)-3)/7 for i in range(len(used))]
            form=sum(conj(z[i])*C[i,j]*z[j] for i in range(len(z)) for j in range(len(z)))
            ref=f.rawjet(b,dict(zip(used,z)))[2];checks.append(abs(form-ref))
        C=cache[key]
        ids=[f.index(*e) for e in used]
        for i,(ii,pi) in enumerate(ids):
            for j,(jj,pj) in enumerate(ids):
                if C[i,j]:D.put(ii,jj,2*mp.re(h)*conj(pi)*C[i,j]*pj)
    print('raw Hessian templates',len(cache),'max check',fmt(max(checks,default=0)),flush=True)
    return D,max(checks,default=0)

def corrected_aug(f,D):
    n=f.n;h=f.H.n;DG=D.mul(f.G)
    DE=D.sub(f.e,f.e);DV=DG.sub(f.e,range(h));DZ=f.G.star().mul(DG)
    a=f.aug.plus(Sp(f.aug.n,f.aug.n))
    a.block(DE,0,0,-1);a.block(DV,0,n);a.block(DV.star(),n,0);a.block(DZ,n,n,-1)
    return a

def ordering(f):
    n=f.n;h=f.H.n
    keys=[(f.bonds[j][0][0]//2,0,f.bonds[j][0][0]%2,f.bonds[j][0][1:],f.bonds[j][1]) for j in f.e]
    keys += [(f.p//2+i//7,1,i%7) for i in range(h)]
    keys += [(f.p//2+i//7,2,i%7) for i in range(h)]
    return sorted(range(n+2*h),key=keys.__getitem__)

def inertia(A,order):
    """Hermitian sparse LDL with scalar and 2x2 pivots at working precision.
    Singular pivots cause an error rather than silent sign invention.
    """
    t0=time.time();n=A.n;rev={i:k for k,i in enumerate(order)};r=[{} for _ in range(n)]
    for i,row in enumerate(A.r):
        k=rev[i]
        for j,v in row.items():r[k][rev[j]]=(v+conj(A.r[j].get(i,0)))/2
    counts=[0,0];small=mp.inf;maxdeg=0;done=set();pairs=0
    for j in range(n):
        if j in done:continue
        row=r[j];d=mp.re(row.get(j,0))
        neighbors=sorted(k for k in row if k!=j)
        off=max((abs(row[k]) for k in neighbors),default=mp.mpf(0))
        if abs(d)>mp.mpf('0.01')*off and abs(d)>mp.power(10,-mp.mp.dps//2):
            small=min(small,abs(d));counts[int(d<0)]+=1
            entries=[(k,row[k]) for k in neighbors];maxdeg=max(maxdeg,len(entries))
            for ki,(k,v) in enumerate(entries):
                fac=conj(v)/d
                for l,w in entries[ki:]:
                    value=clean(r[k].get(l,0)-fac*w);r[k][l]=value;r[l][k]=conj(value)
            removed=[j]
        else:
            if not neighbors or not off:raise ArithmeticError('zero LDL row '+str(j))
            k=max(neighbors,key=lambda k:abs(row[k]));b=row[k];c=mp.re(r[k].get(k,0));det=d*c-abs(b)**2
            if not det:raise ArithmeticError('singular 2x2 pivot')
            if det<0:counts[0]+=1;counts[1]+=1
            else:counts[int(d+c<0)]+=2
            small=min(small,abs(det)/(abs(d)+abs(c)+2*abs(b)));pairs+=1
            remaining=sorted((set(row)|set(r[k]))-{j,k});maxdeg=max(maxdeg,len(remaining))
            for ii,i in enumerate(remaining):
                u=row.get(i,0);v=r[k].get(i,0)
                fj=(conj(u)*c-conj(v)*conj(b))/det
                fk=(-conj(u)*b+conj(v)*d)/det
                for l in remaining[ii:]:
                    value=clean(r[i].get(l,0)-fj*row.get(l,0)-fk*r[k].get(l,0))
                    r[i][l]=value;r[l][i]=conj(value)
            removed=[j,k];neighbors=remaining
        for k in neighbors:
            for rem in removed:r[k].pop(rem,None)
        for rem in removed:r[rem]={};done.add(rem)
    return dict(positive=counts[0],negative=counts[1],min_abs_pivot=small,two_by_two_pivots=pairs,max_front=maxdeg,seconds=time.time()-t0)

def bmin(f,aug=None):
    # Diagnostic double-precision carrier action after exact mp assembly.
    if aug is None:aug=f.aug
    n=f.n;h=f.H.n;K=aug.sub(range(n),range(n)).scipy()
    V=-aug.sub(range(n),range(n,n+h)).scipy();Z=aug.sub(range(n,n+h),range(n,n+h)).scipy()
    F=f.F.scipy();H=f.H.scipy();hl=splu(H)
    def apply(v):
        u=hl.solve(F@v);return K@v-V@u+F.conj().T@hl.solve(Z@u-V.conj().T@v)
    op=LinearOperator((n,n),matvec=apply,dtype=complex)
    vals,vecs=eigsh(op,k=1,which='SA',tol=1e-9,maxiter=2500,v0=np.random.default_rng(127).normal(size=n))
    return float(vals[0]),float(np.linalg.norm(apply(vecs[:,0])-vals[0]*vecs[:,0]))

def initial(q,R,eps,dps,do_inertia=True,iy=0,iz=0,gap=True):
    mp.mp.dps=dps;e=mp.mpf(eps);t0=time.time()
    f=Family(q,R,e,iy,iz,1).assemble();nf=Family(q,R,e,charge=0).assemble();h,hres=nf.hj()
    D,check=draw(f,h);ca=corrected_aug(f,D)
    # A(0) adds omitted plaquettes, which are PSD. Test stronger B-D PD.
    results=dict(q=q,R=R,epsilon=eps,dps=dps,sector=[iy,iz],raw_hessian_check=check,HtJ_residual=hres,
        source_multiplier_max=max(map(abs,h)),raw_D_rowsum_bound=max(sum(map(abs,r.values())) for r in D.r))
    if do_inertia:
        results['B_inertia']=inertia(f.aug,ordering(f))
        results['B_minus_D_inertia']=inertia(ca,ordering(f))
        expected=dict(positive=f.n+f.H.n,negative=f.H.n)
        results['required_augmented_inertia']=expected
        for name in ['B_inertia','B_minus_D_inertia']:
            assert all(results[name][k]==v for k,v in expected.items())
    if gap:
        results['B_min_double'],results['B_eigen_residual_double']=bmin(f)
        results['B_minus_D_min_double'],results['B_minus_D_eigen_residual_double']=bmin(f,ca)
    else:
        results['double_gap_status']='not attempted in this run; numerical mp inertia is the positivity check'
    results['seconds']=time.time()-t0;results['peak_rss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    path=OUT/f'initial_q{q}_R{R}_e{eps}_p{dps}_s{iy}_{iz}.json'
    path.write_text(json.dumps(jsonable(results),indent=2)+'\n');print('INITIAL',json.dumps(jsonable(results)),flush=True)
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=1);p.add_argument('--R',type=int,default=18)
    p.add_argument('--eps',default='1e-3');p.add_argument('--dps',type=int,default=70)
    p.add_argument('--iy',type=int,default=0);p.add_argument('--iz',type=int,default=0);p.add_argument('--no-inertia',action='store_true')
    a=p.parse_args();initial(a.q,a.R,a.eps,a.dps,not a.no_inertia,a.iy,a.iz)
