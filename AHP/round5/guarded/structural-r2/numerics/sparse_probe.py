#!/usr/bin/env python3
"""Room-condition numerical obstacle test, never a pinned-goal certificate.

Reuse the frozen-formula transcriptions, but avoid dense carrier matrices.
Q' has disjoint site blocks. N is an orthonormal basis of its kernel on Om0.
L = mask_Om0 * lap * N, H = L*L, F = L*grad*E, G = grad*N.
Since Gp*L=N, W*E=E-G*H^-1*F and T*T=F*H^-1*F.
For Delta_in, put K=E*Delta_in*E+mass, V=E*Delta_in*G,
Z=G*Delta_in*G. B is the Schur complement in the sparse Hermitian matrix
[K,-V,-F*; -V*,Z+H,H; -F,H,0]. No inverse of a carrier compression is used.

A lower bound on ||J A^-1 Theta|| is measured by projecting to observable
coordinates whose W rows equal coordinate rows EXACTLY in this transcription.
Their coordinate projection P0 satisfies P0 J=P0. Thus the measured norm
||P0 A^-1 Theta|| <= ||J A^-1 Theta||, without a large/ill-conditioned SVD.
The asserted support relationship is numerical/matrix-transcription evidence;
no exact Lean dictionary or validated roundoff bound is claimed.
"""
import sys
sys.dont_write_bytecode = True
import gc, itertools, json, resource, time
from pathlib import Path
import numpy as np
from scipy.linalg import null_space, eigh, solve, svdvals
from scipy.sparse import coo_matrix, bmat, diags
from scipy.sparse.linalg import splu, LinearOperator, eigsh
from scipy.optimize import brentq
from assembly import adj3, Raw, I, P, assemble
from observe import SingleSlab
from lift_probe import local_raw
from wide_probe import geometry

OUT = Path(__file__).resolve().parent
LIMIT = 1900 * 1024**2
resource.setrlimit(resource.RLIMIT_AS, (LIMIT, LIMIT))


def scatter(blocks, shape):
    rr, cc, vv = [], [], []
    for rows, cols, value in blocks:
        value = np.asarray(value)
        nz = np.nonzero(value)
        rr.extend(np.asarray(rows)[nz[0]])
        cc.extend(np.asarray(cols)[nz[1]])
        vv.extend(value[nz])
    out = coo_matrix((vv, (rr, cc)), shape=shape, dtype=complex).tocsc()
    out.eliminate_zeros()
    return out


def gram(lat, u, p):
    x, mu, nu = p
    re, im = lat._re_im(u, p)
    aa = np.zeros((4, 12, 2, 2), complex)
    aa[0, 6:9] = -np.array([P.rmap(u[(x, nu)], e) for e in P.E])
    aa[1, 9:12] = -np.asarray(P.E)
    aa[2, 0:3] = np.asarray(P.E)
    aa[3, 3:6] = np.array([P.rmap(u[(x, mu)], e) for e in P.E])
    c = aa.sum(axis=0)
    bil = -np.einsum('iab,jbc,ca->ij', c, c, re-I).real
    for r, s in itertools.combinations(range(4), 2):
        bil += (-1j * (np.einsum('iab,jbc,ca->ij', aa[r], aa[s], im)
                       - np.einsum('jab,ibc,ca->ij', aa[s], aa[r], im))).real
    return (bil+bil.T)/4 - .5*np.einsum('iab,jba->ij', c, c).real


class SparseSector:
    def __init__(self, R, eps, iy=0, iz=0, rawrows=None):
        self.lat = lat = SingleSlab(R)
        self.u = u = lat.config(0, eps)
        self.eps, self.sector = eps, [iy, iz]
        self.n, self.nd, self.ns = len(lat.eidx), lat.dim, 3*len(lat.sites)
        n, nd, ns = self.n, self.nd, self.ns
        self.phase = np.exp(.5j*np.pi*np.array([iy, iz]))
        em = {j:i for i,j in enumerate(lat.eidx)}
        self.em = em
        gradblocks = []
        for i, (x, mu) in enumerate(lat.bonds):
            j = lat.site_index[x]
            xx = list(x); xx[mu] += 1
            k, ph = self.index(xx)
            gradblocks += [(range(3*i, 3*i+3), range(3*j, 3*j+3), -np.eye(3)),
                           (range(3*i, 3*i+3), range(3*k, 3*k+3), ph*adj3(u[(x, mu)]))]
        grad = scatter(gradblocks, (nd, ns))
        self.grad = grad
        # Site-average kernels are a direct sum over disjoint top blocks.
        nblocks = []; col = 0
        raw = Raw(lat, u)
        for y in sorted(lat.lam1):
            ids, av = [], []
            for o in lat.offs:
                xx = tuple(y[j]+o[j] for j in range(3))
                i, ph = self.index(xx)
                ids.extend(range(3*i, 3*i+3))
                tr = raw.hol(raw.u[None], lat.gamma(y, o))[0]
                av.append(ph*adj3(tr)/8)
            avg = np.hstack(av)
            ker = null_space(avg, rcond=1e-12)
            assert np.max(np.abs(avg@ker)) < 1e-14
            nblocks.append((ids, range(col, col+ker.shape[1]), ker))
            col += ker.shape[1]
        self.N = N = scatter(nblocks, (ns, col))
        mask = np.zeros(ns); mask[lat.sidx] = 1
        L = diags(mask) @ (grad.conj().T @ (grad @ N))
        self.H = H = (L.conj().T @ L).tocsc()
        self.hlu = splu(H)
        self.F = F = (L.conj().T @ grad.conj().T[:, lat.eidx]).tocsc()
        self.G = G = (grad @ N).tocsc()
        q0 = scatter([(range(3*i, 3*i+3), [em[3*lat.bond_index[b]+c] for c in range(3)],
                       np.eye(3)) for i,b in enumerate(lat.b0)], (3*len(lat.b0), n))
        if rawrows is None:
            rawrows = [local_raw(lat, u, b) for b in lat.b1]
        self.rawrows = rawrows
        qtblocks = []
        for i, (used, jac) in enumerate(rawrows):
            for j, (x, mu) in enumerate(used):
                k, ph = self.index(x, mu)
                for c in range(3):
                    if 3*k+c in em:
                        qtblocks.append((range(3*i,3*i+3), [em[3*k+c]], ph*jac[:,3*j+c,None]))
        self.qt = qt = scatter(qtblocks, (3*len(lat.b1), n))
        self.mass = mass = q0.conj().T@q0 + 2*qt.conj().T@qt
        self.delta = delta = self.plaq_matrix(u, lat.plaq_in)
        self.K = K = (delta[lat.eidx][:,lat.eidx] + mass).tocsc()
        self.V = V = (delta[lat.eidx] @ G).tocsc()
        self.Z = Z = (G.conj().T @ delta @ G).tocsc()
        self.aug = bmat([[K, -V, -F.conj().T],
                         [-V.conj().T, Z+H, H],
                         [-F, H, None]], format='csc')
        self.lu = splu(self.aug)
        pin = set(lat.plaq_in)
        self.omitted = [p for p in lat.plaquettes if p not in pin and
                        any(b not in lat._zb_set for b in lat.edges_of(p))]
        boundary = sorted({em[3*lat.bond_index[b]+c] for p in self.omitted
                           for b in lat.edges_of(p) for c in range(3)
                           if 3*lat.bond_index[b]+c in em})
        self.boundary = np.array(boundary)
        # On all omitted edges grad*N is identically zero, not just small.
        omitted_edges = sorted({3*lat.bond_index[b]+c for p in self.omitted
                                for b in lat.edges_of(p) for c in range(3)})
        assert G[omitted_edges].nnz == 0
        eb = np.zeros((n,len(boundary)), complex)
        eb[boundary,np.arange(len(boundary))] = 1
        self.eb = eb
        self.X = self.binv(eb)
        self.S = solve(self.X[boundary], np.eye(len(boundary)), assume_a='her')
        self.S = (self.S+self.S.conj().T)/2
        # Exact coordinate rows belonging to the union of rhoT read balls.
        centers = {b[0] for b in lat.b1}
        def dist(x,y):
            return sum(min(abs(x[j]-y[j]),lat.sides[j]-abs(x[j]-y[j])) for j in range(3))
        sites = {x for x in lat.sites if any(dist(x,y)<=8 for y in centers)}
        grown = np.diff(G.tocsr().indptr)
        pure = [em[3*i+c] for i,b in enumerate(lat.bonds) if b[0] in sites
                for c in range(3) if 3*i+c in em and grown[3*i+c] == 0]
        self.pure = np.array(pure)
        assert len(pure) > 0
        self.Y = self.X[pure] @ self.S

    def index(self, x, mu=None):
        lat = self.lat
        ph = self.phase[0]**(x[1]//2) * self.phase[1]**(x[2]//2)
        y = (x[0]%lat.sides[0], x[1]%2, x[2]%2)
        return (lat.site_index[y] if mu is None else lat.bond_index[(y,mu)]), ph

    def plaq_matrix(self, u, ps):
        blocks = []
        for p in ps:
            x, mu, nu = p
            xm=list(x); xm[mu]+=1
            xn=list(x); xn[nu]+=1
            ids, phases = [], []
            for y,d in [(x,mu),(xm,nu),(xn,mu),(x,nu)]:
                j, ph = self.index(y,d)
                ids.extend(range(3*j,3*j+3)); phases.extend([ph]*3)
            phases=np.array(phases)
            val=phases.conj()[:,None]*gram(self.lat,u,p)*phases[None,:]
            blocks.append((ids,ids,val))
        return scatter(blocks, (self.nd,self.nd))

    def shift(self, theta):
        d = self.plaq_matrix(self.lat.config(theta,self.eps), self.omitted)
        idx = self.lat.eidx[self.boundary]
        return d[idx][:,idx].toarray()

    def binv(self, rhs):
        one = rhs.ndim == 1
        if one: rhs = rhs[:,None]
        b = np.zeros((self.aug.shape[0],rhs.shape[1]),complex); b[:self.n] = rhs
        sol = self.lu.solve(b)[:self.n]
        return sol[:,0] if one else sol

    def wapply(self, x):
        b = np.zeros((self.nd,)+x.shape[1:],complex); b[self.lat.eidx] = x
        return b - self.G@self.hlu.solve(self.F@x)

    def bapply(self, x):
        v = self.hlu.solve(self.F@x)
        return self.K@x - self.V@v + self.F.conj().T@self.hlu.solve(
            (self.Z+self.H)@v-self.V.conj().T@x)

    def local_min(self):
        op = LinearOperator((self.n,self.n), matvec=self.bapply, dtype=complex)
        val, vec = eigsh(op, k=1, which='SA', tol=2e-9, maxiter=3000,
                         v0=np.random.default_rng(718).normal(size=self.n))
        return float(val[0]), float(np.linalg.norm(self.bapply(vec[:,0])-val[0]*vec[:,0]))

    def local_unit_check(self):
        rng = np.random.default_rng(912)
        x = rng.normal(size=(self.n,4)) + 1j*rng.normal(size=(self.n,4))
        inv = self.binv(x)
        res = float(np.linalg.norm(self.bapply(inv)-x)/np.linalg.norm(x))
        pivot = float(np.min(np.abs(self.lu.U.diagonal())))
        assert res < 1e-10 and pivot > 1e-8
        return dict(local_augmented_min_abs_LU_pivot=pivot,local_inverse_relative_residual=res)

    def direct_solve(self, theta, rhs):
        th=self.shift(theta)
        d=scatter([(self.boundary,self.boundary,th)], (self.n,self.n))
        aug=self.aug+bmat([[d,None,None],[None,0*self.H,None],[None,None,0*self.H]],format='csc')
        lu=splu(aug)
        bb=np.zeros((aug.shape[0],rhs.shape[1]),complex);bb[:self.n]=rhs
        x=lu.solve(bb)[:self.n]
        ax=self.bapply(x);ax[self.boundary]+=th@x[self.boundary]
        return x,float(np.linalg.norm(ax-rhs,2))


def small_check():
    eps=1/7680
    s=SparseSector(2,eps)
    raw,w,fixed,hj,checks=assemble(s.lat,eps)
    b=w.T@s.lat.delta_matrix(s.u,'in')@w+fixed
    rng=np.random.default_rng(12);xx=rng.normal(size=(s.n,5))
    report=dict(B_apply_error=float(np.max(np.abs(s.bapply(xx)-b@xx))),
                W_apply_error=float(np.max(np.abs(s.wapply(xx)-w@xx))),
                B_inverse_error=float(np.max(np.abs(s.X-solve(b,s.eb,assume_a='pos')))),
                qtop_error=float(np.max(np.abs(s.qt.toarray()-raw.jac(2e-5)))))
    dense_shift=w.T@(s.lat.delta_matrix(s.lat.config(.5,eps),'all')-
                     s.lat.delta_matrix(s.u,'in'))@w
    th=np.zeros_like(dense_shift,complex);th[np.ix_(s.boundary,s.boundary)]=s.shift(.5)
    report['shift_error']=float(np.max(np.abs(th-dense_shift)))
    report['pure_observation_rows']=len(s.pure)
    report['pure_row_error']=float(np.max(np.abs(w[s.lat.eidx[s.pure]]-np.eye(s.n)[s.pure])))
    assert max(v for k,v in report.items() if k.endswith('error'))<2e-8
    # Independent dense all-sector implementation, including non-real phases.
    import lift_probe
    lift_probe.WideSlab=SingleSlab
    report['complex_sector_checks']=[]
    for iy,iz in [(0,1),(1,2)]:
        sec=SparseSector(2,eps,iy,iz,s.rawrows)
        mat=sec.bapply(np.eye(sec.n,dtype=complex))
        mat[np.ix_(sec.boundary,sec.boundary)]+=sec.shift(.5)
        eigen=eigh((mat+mat.conj().T)/2,eigvals_only=True)
        dense=lift_probe.sector(2,eps,.5,iy,iz,s.rawrows)
        err=float(np.max(np.abs(eigen[:6]-dense['lowest_six'])))
        assert err<1e-10
        report['complex_sector_checks'].append(dict(sector=[iy,iz],lowest_six_error=err,
                                                    **sec.local_unit_check()))
        del sec,mat;gc.collect()
    report['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    report['address_space_limit_bytes']=resource.getrlimit(resource.RLIMIT_AS)[0]
    (OUT/'sparse_small_check.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report),flush=True)


def run(R=18, all_sectors=False):
    start=time.time(); eps=1/7680
    s=SparseSector(R,eps)
    bmin,bres=s.local_min()
    assert bmin>1e-3
    root=brentq(lambda t:eigh(s.S+s.shift(t),eigvals_only=True)[0],0,np.pi,xtol=2e-14)
    ev,v=eigh(s.S+s.shift(root));v=v[:,np.argmin(np.abs(ev))]
    z=s.X@(s.S@v);z/=np.linalg.norm(z)
    az=s.bapply(z);az[s.boundary]+=s.shift(root)@z[s.boundary]
    out=dict(status='floating-point diagnostic, not an exact unit or unboundedness proof',
             R=R,m=1,ell=2,M=2,k=1,a=1,cap=1,alpha=1/48,epsilon=eps,
             room=34<=2*R,geometry=geometry(R),sector=[0,0],
             physical_fine_sides=[12*R+16,8,8],cell_sides=list(s.lat.sides),
             carrier_dimension=s.n,augmented_dimension=s.aug.shape[0],augmented_nnz=s.aug.nnz,
             boundary_dimension=len(s.boundary),pure_observation_rows=len(s.pure),
             pure_site_longitudinal_range=[min(s.lat.bonds[s.lat.eidx[i]//3][0][0] for i in s.pure),
                                           max(s.lat.bonds[s.lat.eidx[i]//3][0][0] for i in s.pure)],
             local_min=bmin,local_eigen_residual=bres,carrier_crossing=root,
             crossing_residual=float(np.linalg.norm(az)),
             crossing_J_norm_lower_bound=float(np.linalg.norm(z[s.pure])),
             rows=[],sectors=[])
    for d in [1e-2,1e-3,1e-4,1e-5,1e-6,1e-7]:
        t=root-d;th=s.shift(t);hs=s.S+th
        f=s.Y@solve(hs,th,assume_a='her')
        norm=float(svdvals(f)[0])
        direct,res=s.direct_solve(t,s.eb@th)
        err=float(np.linalg.norm(direct[s.pure]-f,2)/norm)
        row=dict(offset=d,theta=t,observed_transfer_lower_bound=norm,offset_times_bound=d*norm,
                 carrier_Schur_min=float(eigh(hs,eigvals_only=True)[0]),
                 schur_vs_direct_relative_error=err,direct_solve_residual=res)
        out['rows'].append(row);print(json.dumps(row),flush=True)
    assert all(r['carrier_Schur_min']>0 for r in out['rows'])
    assert max(r['schur_vs_direct_relative_error'] for r in out['rows'])<1e-5
    assert out['rows'][-1]['observed_transfer_lower_bound']>10000*out['rows'][0]['observed_transfer_lower_bound']
    out['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result=OUT/f'sparse_R{R}_results.json'
    result.write_text(json.dumps(out,indent=2))
    if all_sectors:
        rawrows=s.rawrows;theta=root-1e-7
        for iy,iz in itertools.product(range(4),repeat=2):
            if [iy,iz]==[0,0]:
                sec=s;emin,eres=bmin,bres
            else:
                sec=SparseSector(R,eps,iy,iz,rawrows)
                emin,eres=None,None
            schur=float(eigh(sec.S+sec.shift(theta),eigvals_only=True)[0])
            row=dict(sector=[iy,iz],carrier_dimension=sec.n,local_min=emin,
                     local_eigen_residual=eres,carrier_Schur_min=schur,
                     **sec.local_unit_check())
            print(json.dumps(row),flush=True);out['sectors'].append(row)
            assert schur>0
            result.write_text(json.dumps(out,indent=2))
            if sec is not s: del sec
            gc.collect()
    out['seconds']=time.time()-start
    out['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    out['address_space_limit_bytes']=resource.getrlimit(resource.RLIMIT_AS)[0]
    result.write_text(json.dumps(out,indent=2))
    print('DONE',out['seconds'],out['peak_rss_kib'],flush=True)

if __name__=='__main__':
    if '--check' in sys.argv:small_check()
    else:run(18, '--all-sectors' in sys.argv)
