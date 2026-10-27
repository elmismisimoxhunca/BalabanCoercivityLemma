#!/usr/bin/env python3
"""High-precision evidence on the finite exterior star; no proof/certification.
Reconstruct the physical first top-layer jets from ALL Fourier characters.
Full augmented inverses precede restriction. Exact Taylor algebra, no finite differences.
"""
import sys
sys.dont_write_bytecode=True
from star_probe import *
from probe import Refine, conj
import gc


def hessian_mp(t):
    cs=[-mp.exp(2j*t),mp.mpf(1),mp.mpf(1)]
    m=mp.matrix(3)
    for r in range(3):
        for s in range(3): m[r,s]=mp.cos(t)*conj(cs[r])*cs[s]
    for r in range(3):
        for s in range(r+1,3):
            v=1j*mp.sin(t)*conj(cs[r])*cs[s]
            m[r,s]+=v; m[s,r]+=conj(v)
    return m


def patch_mp(t, plaquettes, bonds):
    m=mp.matrix(len(bonds)); hh=hessian_mp(t)
    for _,_,es in plaquettes:
        ids=[bonds.index(b) for b in es]
        for i in range(3):
            for j in range(3):m[ids[i],ids[j]]+=hh[i,j]
    return m


def jet_run(q,R,dps):
    mp.mp.dps=dps; start=time.time()
    plaquettes,bonds=patch_data(4*q); n=len(bonds); nc=(4*q)**2
    C=mp.matrix(n); sector_rows=[]; max_res=mp.mpf(0)
    for iy in range(4*q):
        for iz in range(4*q):
            f=Family(q,R,mp.mpf(0),iy,iz,1).assemble()
            ext,_=f.plaq('out',0)
            for i,row in enumerate(ext.r):
                if i not in f.em:continue
                for j,v in row.items():
                    if j in f.em:f.aug.put(f.em[i],f.em[j],v)
            targets=[((f.p,0,0),d) for d in [0,1,2]]
            used=set()
            for b in targets:
                base,legs=f.rawdata[b]
                used.update(base)
                for l,m,r in legs:used.update(l+m+r)
            used=sorted(used)
            idx_phase=[f.index(*b) for b in bonds]
            solver=Refine(f.aug); columns=[]
            for col,(j,ph) in enumerate(idx_phase):
                rhs=[0]*f.aug.n;rhs[f.em[j]]=conj(ph)
                sol=solver.solve(rhs)
                max_res=max(max_res,solver.history[-1][-1])
                for row,(k,p) in enumerate(idx_phase):C[row,col]+=p*sol[f.em[k]]/nc
                w=f.dressed(sol[:f.n],sol[f.n:f.n+f.H.n])
                columns.append([w[f.index(*e)[0]] for e in used])
            sector_rows.append((f.ph,used,columns))
            print('SECTOR',iy,iz, 'seconds', round(time.time()-start,2),flush=True)
            del solver,sol,w;gc.collect()
    C=(C+C.H)/2;S=C**-1;base=patch_mp(mp.mpf(0),plaquettes,bonds)
    def pencil(t):return S+patch_mp(t,plaquettes,bonds)-base
    def low(t):return mp.eighe(pencil(t),eigvals_only=True)[0]
    root=mp.findroot(low,(mp.mpf('1.15'),mp.mpf('1.25')),tol=mp.power(10,-dps+12),verify=True)
    eig,vecs=mp.eighe(pencil(root));v=vecs[:,0]
    drive=-(patch_mp(root,plaquettes,bonds)-base)*v
    compressed=[]
    for phases,used,cols in sector_rows:
        compressed.append((phases,used,[sum(cols[j][i]*drive[j] for j in range(n)) for i in range(len(used))]))
    totals=[mp.mpf(0)]*3;mx=[mp.mpf(0)]*3
    for cy in range(4*q):
        for cz in range(4*q):
            field={e:mp.mpc(0) for e in compressed[0][1]}
            for phases,used,w in compressed:
                for e,z in zip(used,w):
                    x,d=e
                    phase=phases[0]**(x[1]//2+cy)*phases[1]**(x[2]//2+cz)
                    field[e]+=phase*z/nc
            for d,b in enumerate(targets):
                val=f.rawjet(b,field)[2]
                totals[d]+=val;mx[d]=max(mx[d],abs(val))
    result=dict(q=q,R=R,dps=dps,root=mp.nstr(root,dps-5),next_eigenvalue=mp.nstr(eig[1],30),first_top_jet_sums=[mp.nstr(x,dps-5) for x in totals],max_abs_first_top_jet=[mp.nstr(x,dps-5) for x in mx],residual=mp.nstr(max_res,dps-5),boundary_null_residual=mp.nstr(mp.mnorm(pencil(root)*v,1),dps-5),seconds=time.time()-start,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,method='all-character full augmented solves; physical transverse reconstruction; exact Taylor jet',caveat='floating-point, not intervals; not a Lean normalization dictionary or cofinal proof')
    (Path(__file__).parent/f'starjet_q{q}_R{R}_p{dps}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,default=1);ap.add_argument('--R',type=int,default=18);ap.add_argument('--dps',type=int,default=60)
    a=ap.parse_args();jet_run(a.q,a.R,a.dps)
