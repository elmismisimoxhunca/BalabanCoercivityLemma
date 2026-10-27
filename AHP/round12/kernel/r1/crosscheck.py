#!/usr/bin/env python3
"""Held-out full-character screen and high-precision kernel check. Evidence only.
Uses the R6 transcription read-only; nothing in this script is a Lean certificate.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'AHP/round6/probe'))
from probe import Family, mp, np, jsonable
from leading_source import leading_h
import resource, argparse, json, time, gc
from scipy.sparse.linalg import splu
from scipy.linalg import eigvalsh
resource.setrlimit(resource.RLIMIT_AS, (2*1024**3, 2*1024**3))
OUT = Path(__file__).resolve().parent

class LeftFamily(Family):
    def angle(self, b, t=0):
        x, d = b
        y = self.shift(x, d)
        if not (self.in0(x) or self.in0(y)):
            return t if x[0] % self.nx < self.lo else 0
        return 0

def pencil(f):
    t0,t1,t2 = f.theta(0),f.theta(mp.pi/2),f.theta(mp.pi)
    C,A = (t0+t2)/2,(t0-t2)/2
    B = t1-C
    return C,A,B

def screen(q,R):
    start=time.time();mp.mp.dps=25
    t=mp.mpf('0.563971517985560942179715334361600')
    result={'mode':'all-character screen', 'q':q,'R':R,'assembly_dps':25,
      'spectral_precision':'IEEE double','angle':str(t),'sectors':[],
      'qualification':'Floating-point screen only; not certified inertia or cofinality.'}
    target=OUT/f'screen_q{q}_R{R}.json'
    for charge in [0,1]:
      for iy in range(4*q):
       for iz in range(4*q):
        f=LeftFamily(q,R,mp.mpf(0),iy,iz,charge).assemble()
        M=f.aug.scipy(); lu=splu(M)
        rhs=np.zeros((f.aug.n,len(f.boundary)),complex)
        rhs[f.boundary,np.arange(len(f.boundary))]=1
        X=lu.solve(rhs)
        residual=float(np.max(np.abs(M@X-rhs)))
        C0=X[f.boundary]; S=np.linalg.inv(C0); S=(S+S.conj().T)/2
        C,A,B=[np.array(m.tolist(),complex) for m in pencil(f)]
        def at(s):return S+C+np.cos(s)*A+np.sin(s)*B
        vals=eigvalsh(at(float(t)))
        result['sectors'].append({'charge':charge,'character':[iy,iz],
          'at_root_low':vals[:3].tolist(),'at_zero_min':float(eigvalsh(at(0))[0]),
          'at_pi_min':float(eigvalsh(at(np.pi))[0]),'solve_residual':residual})
        result['seconds']=time.time()-start
        result['peak_rss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        target.write_text(json.dumps(result,indent=2)+'\n')
        print('SCREEN',charge,iy,iz,vals[:3],flush=True)
        del f,M,lu,rhs,X,C0,S,C,A,B;gc.collect()
    result['complete']=True
    target.write_text(json.dumps(result,indent=2)+'\n')

def precise(q,R,iy,iz,charge,dps,find_root):
    start=time.time();mp.mp.dps=dps
    f=LeftFamily(q,R,mp.mpf(0),iy,iz,charge).assemble()
    S=f.boundary_inverse();C,A,B=pencil(f)
    theta=lambda t:C+mp.cos(t)*A+mp.sin(t)*B
    if find_root:
      t=mp.findroot(lambda t:mp.eighe(S+theta(t),eigvals_only=True)[0],
        (mp.mpf('.55'),mp.mpf('.58')),tol=mp.power(10,-dps+15),verify=True)
    else:
      ref=json.loads((OUT/f'precise_q{q}_R{R}_s7_7_c1_p230.json').read_text())
      t=mp.mpf(ref['root'])
    vals,V=mp.eighe(S+theta(t)); y=V[:,0]; rhs=S*y
    x=[sum(f.X[j][i]*rhs[j] for j in range(len(f.X))) for i in range(f.aug.n)]
    nrm=mp.sqrt(sum(abs(z)**2 for z in x[:f.n]));x=[z/nrm for z in x]
    residual=f.aug.apply(x)
    bd=theta(t)*mp.matrix([x[i] for i in f.boundary])
    for i,b in enumerate(f.boundary):residual[b]+=bd[i]
    bv=mp.matrix([x[i] for i in f.boundary])
    slope=mp.re((bv.H*(-mp.sin(t)*A+mp.cos(t)*B)*bv)[0])
    out={'mode':'high-precision selected block','q':q,'R':R,'character':[iy,iz],
      'charge':charge,'dps':dps,'root':t,'root_solved':find_root,
      'schur_low':[mp.re(v) for v in vals[:4]],'kernel_form_slope':slope,
      'augmented_residual':max(map(abs,residual)),
      'pencil_error':mp.mnorm(f.theta(mp.mpf('.321'))-theta(mp.mpf('.321')),1),
      'qualification':'Non-interval numerical evidence in the R6 cell transcription. No Lean Fourier identification, full-kernel proof, or cofinal result.'}
    if find_root:
      w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n])
      c1,terms=f.correction(w,leading_h(f))
      jets=[]
      for b in f.b1:
        base,legs=f.rawdata[b]; used=set(base)
        for l,m,r in legs:used.update(l+m+r)
        field={e:w[f.index(*e)[0]]*f.index(*e)[1] for e in used}
        jets.append(f.rawjet(b,field)[2])
      # A pure-real-color physical field has zero circular polarization.
      # For a non-self-conjugate character its full-torus sum of z^2 is exactly
      # zero by character orthogonality; independently sum phases at high precision.
      phase_square_sum=sum(f.ph[0]**(2*a)*f.ph[1]**(2*b)
        for a in range(4*q) for b in range(4*q))/(4*q)**2
      out.update(canonical_coupling=c1,first_tangential_jet=jets[2],
        max_top_jet=max(map(abs,jets)),jet_norm_sq=sum(abs(v)**2 for v in jets),
        residual_over_coupling=out['augmented_residual']/abs(c1),
        full_torus_color_anisotropy=abs(sum(z*z for z in x[:f.n])*phase_square_sum),
        phase_square_sum=abs(phase_square_sum),
        left_half_mass=sum(abs(x[i])**2 for i,j in enumerate(f.e)
          if f.bonds[j][0][0]<(f.lo+f.hi)/2))
    out['seconds']=time.time()-start
    out['peak_rss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    target=OUT/f'precise_q{q}_R{R}_s{iy}_{iz}_c{charge}_p{dps}.json'
    target.write_text(json.dumps(jsonable(out),indent=2)+'\n')
    print('RESULT',target,json.dumps(jsonable(out),indent=2),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['screen','precise'])
    p.add_argument('--q',type=int,default=2);p.add_argument('--R',type=int,default=32)
    p.add_argument('--iy',type=int,default=7);p.add_argument('--iz',type=int,default=7)
    p.add_argument('--charge',type=int,default=1);p.add_argument('--dps',type=int,default=190)
    p.add_argument('--competitor',action='store_true');a=p.parse_args()
    if a.mode=='screen':screen(a.q,a.R)
    else:precise(a.q,a.R,a.iy,a.iz,a.charge,a.dps,not a.competitor)
