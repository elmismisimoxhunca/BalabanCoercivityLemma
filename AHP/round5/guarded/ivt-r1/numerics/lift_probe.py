#!/usr/bin/env python3
"""Evidence only: all 16 transverse Fourier sectors of the period-two lift.

Actual-formula numerical transcriptions, not certified Lean operator equality.
Frozen source anchors under lean/src/ (additional detail: assembly.py header):
 grad/curl/transport: AdalyFormal/Balaban/CovariantOperators.lean:247,301,315;
 plaquette quadratic form: ZLocOps.lean:119,181,186; DeltaPrimeOperator:287-395;
 site projector/padded inverse: R2Ops1.lean:135,141,150,166,170,
 ZR2Ops2.lean:27,63; W and T: ZR2Ops2.lean:67,100;
 raw map: R2Raw1.lean:36,43,68,74; jets: R2RawX.lean:187,
 ZLocJet.lean:35,39,89,100; assembled Q: ZXR2Sector.lean:97,109;
 mass/base data: ZXR2Ops3.lean:98,102,134; Ginv: R2Algebra.lean:145;
 correction/root from corrected_probe: R2Algebra.lean:149,212,220,222.
Geometry: r2-refute/Attempt.lean:377,380,385 (copied verbatim in our Attempt).

Each sector is assembled BEFORE inverses. Boundary phases on raw paths are
retained using lifted edge coordinates, not inferred from the quotient matrix.
The scalar correction root is recomputed in the zero sector. Only carrier
spectra are computed for other sectors; corrected singularity outside the zero
sector is not required for a candidate, but the full guard is. No exact spectral,
class-regularity, lift-intertwining, or cofinal theorem follows from these data.
1900 MiB address-space cap is installed by assembly.py. Single-thread BLAS.
"""
import sys
sys.dont_write_bytecode=True
import gc,itertools,json,time,resource
from types import SimpleNamespace
from pathlib import Path
import numpy as np
from scipy.linalg import eigh,null_space,orth,solve
from scipy.sparse import coo_matrix
from assembly import Raw,adj3,P,I
from crossing import SingleSlab as WideSlab
from jet2 import raw_jet
from corrected_probe import run as corrected_run
OUT=Path(__file__).resolve().parent


def local_raw(lat,U,c):
    """A single raw output with unwrapped transverse path coordinates."""
    x,mu=c
    def shift(x,mu,n=1):
        y=list(x); y[mu]+=n
        if mu==0:y[mu]%=lat.sides[0]
        return tuple(y)
    def path(x,dirs):
        ans=[]
        for d in dirs:ans.append((x,d));x=shift(x,d)
        return ans
    def gamma(x,o):return path(x,[d for d in (2,1,0) for _ in range(o[d])])
    xp=shift(x,mu,2);base=path(x,[mu,mu]);legs=[]
    for o in lat.offs:
        xx=tuple((x[j]+o[j])%lat.sides[0] if j==0 else x[j]+o[j] for j in range(3))
        legs.append((gamma(x,o),path(xx,[mu,mu]),gamma(xp,o)))
    used=sorted(set(base).union(*(set(l+m+r) for l,m,r in legs)))
    ix={b:i for i,b in enumerate(used)};cv=lambda p:[ix[b] for b in p]
    raw=Raw.__new__(Raw);raw.lat=SimpleNamespace(nB=len(used),dim=3*len(used))
    raw.u=np.asarray([U[((b[0][0],b[0][1]%2,b[0][2]%2),b[1])] for b in used])
    raw.data=[(cv(base),[(cv(l),cv(m),cv(r)) for l,m,r in legs])]
    raw.bg=[raw.blocked(raw.u[None],raw.data[0])[0]]
    h=2e-5;eye=np.eye(raw.lat.dim)
    J=raw_jet(raw,eye)[1].T
    return used,J


def sector(R,eps,theta,iy,iz,rawrows):
    lat=WideSlab(R);U=lat.config(0,eps);Ua=lat.config(theta,eps)
    n=lat.dim;ns=3*len(lat.sites);phase=np.exp(.5j*np.pi*np.array([iy,iz]))
    def index_phase(x,mu=None):
        x=(x[0]%lat.sides[0],x[1],x[2])
        p=phase[0]**(x[1]//2)*phase[1]**(x[2]//2)
        y=(x[0],x[1]%2,x[2]%2)
        return (lat.site_index[y] if mu is None else lat.bond_index[(y,mu)]),p
    def shift(x,mu):
        y=list(x);y[mu]+=1;return tuple(y)
    grad=np.zeros((n,ns),complex)
    for i,(x,mu) in enumerate(lat.bonds):
        j=lat.site_index[x];k,p=index_phase(shift(x,mu))
        grad[3*i:3*i+3,3*j:3*j+3]-=np.eye(3)
        grad[3*i:3*i+3,3*k:3*k+3]+=adj3(U[(x,mu)])*p
    emap={j:i for i,j in enumerate(lat.eidx)};ne=len(lat.eidx)
    q0=np.zeros((3*len(lat.b0),ne),complex)
    for i,b in enumerate(lat.b0):
        j=lat.bond_index[b]
        for c in range(3):q0[3*i+c,emap[3*j+c]]=1
    qt=np.zeros((3*len(lat.b1),ne),complex)
    for i,(used,J) in enumerate(rawrows):
        for j,(x,mu) in enumerate(used):
            k,p=index_phase(x,mu)
            for c in range(3):
                if 3*k+c in emap:qt[3*i:3*i+3,emap[3*k+c]]+=p*J[:,3*j+c]
    raw=Raw(lat,U);qp=[];weights=[]
    for x in sorted(lat.lam0):
        b=np.zeros((3,ns),complex);i=lat.site_index[x];b[:,3*i:3*i+3]=np.eye(3)
        qp.append(b);weights.extend([1.]*3)
    for y in sorted(lat.lam1):
        b=np.zeros((3,ns),complex)
        for o in lat.offs:
            x=tuple(y[j]+o[j] for j in range(3));i,p=index_phase(x)
            t=raw.hol(raw.u[None],lat.gamma(y,o))[0]
            b[:,3*i:3*i+3]+=p*adj3(t)/8
        qp.append(b);weights.extend([2.]*3)
    qp=np.vstack(qp);lap=grad.conj().T@grad;mask=lat.sidx
    nq=null_space(qp[:,mask],rcond=1e-10)
    ri=orth(lap[np.ix_(mask,mask)]@nq,rcond=1e-10)
    proj=np.zeros_like(lap);proj[np.ix_(mask,mask)]=ri@ri.conj().T
    mat=lap+qp.conj().T@(np.array(weights)[:,None]*qp)
    gp=np.zeros_like(lap);gp[np.ix_(mask,mask)]=solve(mat[np.ix_(mask,mask)],np.eye(len(mask)),assume_a='her')
    W=np.eye(n)[:,lat.eidx]-grad@gp@proj@grad.conj().T[:,lat.eidx]
    T=proj@grad.conj().T[:,lat.eidx]
    A=T.conj().T@T+q0.conj().T@q0+2*qt.conj().T@qt
    # Local plaquette scatter; phases kept on all four edges.
    rr=[];cc=[];vv=[]
    for x,mu,nu in lat.plaquettes:
        re,im=lat._re_im(Ua,(x,mu,nu));aa=np.zeros((4,12,2,2),complex)
        aa[0,6:9]=-np.array([P.rmap(Ua[(x,nu)],e) for e in P.E]);aa[1,9:12]=-np.asarray(P.E)
        aa[2,0:3]=np.asarray(P.E);aa[3,3:6]=np.array([P.rmap(Ua[(x,mu)],e) for e in P.E])
        c=aa.sum(axis=0);bil=-np.einsum('iab,jbc,ca->ij',c,c,re-I).real
        for r,s in itertools.combinations(range(4),2):
            bil+=(-1j*(np.einsum('iab,jbc,ca->ij',aa[r],aa[s],im)-np.einsum('jab,ibc,ca->ij',aa[s],aa[r],im))).real
        gram=(bil+bil.T)/4-.5*np.einsum('iab,jba->ij',c,c).real
        edges=[(x,mu),(shift(x,mu),nu),(shift(x,nu),mu),(x,nu)]
        ids=[];ph=[]
        for y,d in edges:
            j,p=index_phase(y,d);ids.extend(range(3*j,3*j+3));ph.extend([p]*3)
        ph=np.array(ph);g=ph.conj()[:,None]*gram*ph[None,:]
        rr.extend(np.repeat(ids,12));cc.extend(np.tile(ids,12));vv.extend(g.ravel())
    delta=coo_matrix((vv,(rr,cc)),shape=(n,n)).tocsr()
    A+=W.conj().T@(delta@W)
    herm=float(np.max(np.abs(A-A.conj().T)));A=(A+A.conj().T)/2
    ev=eigh(A,eigvals_only=True)
    return dict(sector=[iy,iz],dimension=ne,min_abs=float(np.min(np.abs(ev))),
        lowest_six=ev[:6].tolist(),negative_count=int(np.sum(ev<0)),hermitian_error=herm,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)

if __name__=='__main__':
    start=time.time();R=2;eps=.04
    single='--single' in sys.argv
    if single:
        class SingleSlab(WideSlab):
            def config(self,theta,eps):
                u=super().config(theta,eps)
                u[((self.p+1,1,0),2)]=I.copy()
                return u
        WideSlab=SingleSlab
        import corrected_probe
        corrected_probe.WideSlab=SingleSlab
    result_file=OUT/('lift_single_results.json' if single else 'lift_results.json')
    candidate=corrected_run(R,eps);gc.collect()
    payload=dict(status='floating-point candidate only',single_defect=single,candidate=candidate,sectors=[])
    result_file.write_text(json.dumps(payload,indent=2))
    lat=WideSlab(R);u=lat.config(0,eps)
    rows=[local_raw(lat,u,c) for c in lat.b1]
    qref=Raw(lat,u).jac(2e-5);q=np.zeros_like(qref);em={j:i for i,j in enumerate(lat.eidx)}
    for i,(used,J) in enumerate(rows):
        for j,(x,mu) in enumerate(used):
            b=((x[0],x[1]%2,x[2]%2),mu);idx=lat.bond_index[b]
            for c in range(3):
                if 3*idx+c in em:q[3*i:3*i+3,em[3*idx+c]]+=J[:,3*j+c]
    payload['zero_sector_jacobian_difference']=float(np.max(np.abs(q-qref)))
    # Summing partial finite differences differs from the simultaneous quotient derivative by O(h^2).
    assert payload['zero_sector_jacobian_difference']<2e-8
    del q,qref
    for iy,iz in itertools.product(range(4),repeat=2):
        row=sector(R,eps,candidate['corrected_root'],iy,iz,rows)
        payload['sectors'].append(row);print(json.dumps(row),flush=True);gc.collect()
        result_file.write_text(json.dumps(payload,indent=2))
    payload['seconds']=time.time()-start
    payload['minimum_carrier_abs_over_all_sectors']=min(r['min_abs'] for r in payload['sectors'])
    payload['total_fiber_dimension']=sum(r['dimension'] for r in payload['sectors'])
    payload['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result_file.write_text(json.dumps(payload,indent=2))
    print('DONE',payload['seconds'],payload['minimum_carrier_abs_over_all_sectors'],flush=True)
