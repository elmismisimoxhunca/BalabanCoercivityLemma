#!/usr/bin/env python3
"""All characters: mp-assembled operators with DOUBLE spectral screening.
This file does not claim arbitrary-precision full-sector certification.
SOURCES.md gives all Lean anchors; positivity.py supplies genuine D.
"""
import sys
sys.dont_write_bytecode = True
from positivity import *
from scipy.sparse import bmat,eye
from scipy.linalg import eigvalsh

def double_inertia(f,a):
    from scipy.sparse import block_diag
    from scipy.linalg import qr
    n=f.n;h=f.H.n;order=ordering(f)
    # Local orthogonal congruences avoid the structural zero scalar pivots
    # of the saddle system, without changing its inertia. All arithmetic
    # in this SCREEN is double; mp LDL is checked separately in sector zero.
    def cell(i):
        return f.bonds[f.e[i]][0][0]//2 if i<n else f.p//2+((i-n)%h)//7
    groups=[len(list(g)) for _,g in itertools.groupby(order,key=cell)]
    rng=np.random.default_rng(731)
    P=block_diag([qr(rng.normal(size=(g,g)))[0] for g in groups],format='csc')
    aa=a.scipy()[order][:,order];aa=(P.T@aa@P).tocsc();aa=(aa+aa.conj().T)/2
    lu=splu(aa,permc_spec='NATURAL',diag_pivot_thresh=0,options={'Equil':False})
    if np.any(lu.perm_r!=np.arange(aa.shape[0])):raise ArithmeticError('unexpected row pivot')
    piv=lu.U.diagonal()
    relimag=float(np.max(abs(piv.imag)/(1+abs(piv.real))))
    if relimag>1e-6 or np.min(np.abs(piv.real))<1e-8:raise ArithmeticError('uncertain LU inertia '+str((relimag,float(np.min(abs(piv.real))),float(np.max(abs(piv.imag))))))
    return dict(positive=int(np.sum(piv.real>0)),negative=int(np.sum(piv.real<0)),min_abs_pivot=float(np.min(abs(piv))),max_imag_pivot=float(np.max(abs(piv.imag))),max_relative_imag_pivot=relimag)

def scan(q,R,eps,dps=70):
    mp.mp.dps=dps;e=mp.mpf(eps);start=time.time()
    files=sorted(OUT.glob(f'q{q}_R{R}_e{eps}_p*_s0_0.json'))
    zero=max((json.loads(p.read_text()) for p in files),key=lambda p:p['dps'])
    tc=float(zero['root']);nf=Family(q,R,e,charge=0).assemble();hj,_=nf.hj()
    report=dict(q=q,R=R,epsilon=eps,assembly_dps=dps,screening_precision='IEEE double (not mpmath eigensolves)',root=zero['root'],sectors=[])
    out=OUT/(f'sectors_q{q}_R{R}_e{eps}'+(f'_p{dps}' if dps!=70 else '')+'.json')
    for charge in [0,1]:
        for iy in range(4*q):
            for iz in range(4*q):
                f=Family(q,R,e,iy,iz,charge).assemble()
                if charge:
                    D,_=draw(f,hj);ca=corrected_aug(f,D)
                else:ca=f.aug  # neutral C2 paired with neutral J is zero.
                pi=double_inertia(f,f.aug);ci=double_inertia(f,ca)
                assert pi['positive']==ci['positive']==f.n+f.H.n and pi['negative']==ci['negative']==f.H.n
                lu=splu(f.aug.scipy());rhs=np.zeros((f.aug.n,len(f.boundary)),complex)
                rhs[f.boundary,np.arange(len(f.boundary))]=1
                X=lu.solve(rhs);C=X[f.boundary];S=np.linalg.inv(C);S=(S+S.conj().T)/2
                theta0=np.array(f.theta(0).tolist(),complex);thetat=np.array(f.theta(mp.mpf(zero['root'])).tolist(),complex)
                l0=float(eigvalsh(S+theta0)[0]);lt=float(eigvalsh(S+thetat)[0])
                # A grid checks the earlier path; high precision handles the
                # near-degenerate zero sector, not double's near-zero signs.
                grid=[float(eigvalsh(S+np.array(f.theta(mp.mpf(k)*mp.mpf(zero['root'])/8).tolist(),complex))[0]) for k in range(8)]
                row=dict(charge=charge,character=[iy,iz],B_inertia=pi,B_minus_D_inertia=ci,
                    initial_boundary_schur_min=l0,at_first_zero_sector_crossing_schur_min=lt,pre_crossing_grid_min=min(grid))
                report['sectors'].append(row)
                report['seconds']=time.time()-start
                report['peak_rss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
                out.write_text(json.dumps(report,indent=2)+'\n')
                print('SECTOR',charge,iy,iz,'initial',l0,'crossing',lt,flush=True)
    report['complete']=True;out.write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':scan(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
