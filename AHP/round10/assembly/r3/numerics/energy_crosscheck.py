#!/usr/bin/env python3
"""Held-out actual q=2,R=26 left-twist test of the adaptive curl-energy profile.
Full neutral KKT solves, no tridiagonal replacement. Floating-point evidence only.
Read-only imports; all outputs remain in assembly/r3/numerics.
"""
import os, sys, resource, json, time, argparse
from pathlib import Path
sys.dont_write_bytecode=True
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
ROOT=Path(__file__).resolve().parents[5]
sys.path.insert(0,str(ROOT/'AHP/round10/assembly/r2/numerics'))
from crosscheck import LeftFamily
sys.path.insert(0,str(ROOT/'AHP/round6/probe'))
from probe import Family, Sp, Refine, mp, jsonable
from leading_source import leading_h
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
p=argparse.ArgumentParser();p.add_argument('--dps',type=int,required=True)
dps=p.parse_args().dps;mp.mp.dps=dps;start=time.time()
q,R=2,26
f=LeftFamily(q,R,mp.mpf(0),7,7,1).assemble()
S=f.boundary_inverse()
T0,T1,T2=f.theta(0),f.theta(mp.pi/2),f.theta(mp.pi)
C,A=(T0+T2)/2,(T0-T2)/2;B=T1-C
theta=lambda t:C+mp.cos(t)*A+mp.sin(t)*B
root=mp.findroot(lambda t:mp.eighe(S+theta(t),eigvals_only=True)[0],
                 (mp.mpf('.55'),mp.mpf('.58')),tol=mp.power(10,-dps+15),verify=True)
ev,vec=mp.eighe(S+theta(root));y=vec[:,0];rhs=S*y
x=[sum(f.X[j][i]*rhs[j] for j in range(len(f.X))) for i in range(f.aug.n)]
norm=mp.sqrt(sum(abs(a)**2 for a in x[:f.n]));x=[a/norm for a in x]
w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n])
res=f.aug.apply(x);bd=theta(root)*mp.matrix([x[i] for i in f.boundary])
for i,b in enumerate(f.boundary):res[b]+=bd[i]
nullres=max(map(abs,res));c1,_=f.correction(w,leading_h(f))
z=[]
for b in f.b1:
 base,legs=f.rawdata[b];used=set(base)
 for l,m,r in legs:used.update(l+m+r)
 field={e:w[f.index(*e)[0]]*f.index(*e)[1] for e in used}
 z.append(f.rawjet(b,field)[2])
zscale=max(map(abs,z));zn=[v/zscale for v in z]
# All subsequent solves use scaled jets, so roundoff is not compared with an
# exponentially small energy. Restoring the scale is explicit below.
g=Family(q,R,mp.mpf(0),charge=0).assemble()
assert g.b1==f.b1
na,nc=g.aug.n,g.Q.n
KKT=Sp(na+nc,na+nc);KKT.block(g.aug,0,0);KKT.block(g.Q,na,0);KKT.block(g.Q.star(),0,na)
solve=Refine(KKT)
coarse=[mp.mpf(0)]*len(g.b0)+zn
rhs=[mp.mpf(0)]*na+coarse
sol=solve.solve(rhs)
primal=sol[:g.n]
full=[mp.mpf(0)]*len(g.bonds)
for i,j in enumerate(g.e):full[j]=primal[i]
delta,_=g.plaq();J=delta.apply(full)
energy=mp.re(sum(mp.conj(full[i])*J[i] for i in range(len(full))))
# Independently evaluate circulation squares directly from oriented plaquettes.
curlenergy=mp.mpf(0);maxcurl=mp.mpf(0)
for site in g.sites:
 for mu,nu in [(0,1),(0,2),(1,2)]:
  corners=[site,g.shift(site,mu),g.shift(site,nu),g.shift(g.shift(site,mu),nu)]
  if not all(g.in0(t) for t in corners):continue
  def val(b):
   j,phase=g.index(*b);return full[j]*phase
  curl=val((site,mu))+val((g.shift(site,mu),nu))-val((g.shift(site,nu),mu))-val((site,nu))
  curlenergy+=abs(curl)**2;maxcurl=max(maxcurl,abs(curl))
# The adjoint source solve tests the pairing identity against H*J independently.
source_rhs=[J[i] for i in g.e]+[mp.mpf(0)]*(na+nc-g.n)
source_sol=solve.solve(source_rhs);h=source_sol[na:]
reciprocity=mp.re(sum(mp.conj(coarse[i])*h[i] for i in range(nc)))
reslift=max(map(abs,[a-b for a,b in zip(KKT.apply(sol),rhs)]))
ressource=max(map(abs,[a-b for a,b in zip(KKT.apply(source_sol),source_rhs)]))
qres=max(map(abs,[a-b for a,b in zip(g.Q.apply(primal),coarse)]))
out=dict(q=q,R=R,character=[7,7],twist='left-only',dps=dps,root=root,
 schur_low=[mp.re(a) for a in ev[:4]],canonical_c1=c1,null_residual=nullres,
 null_residual_over_c1=nullres/abs(c1),jet_scale=zscale,
 scaled_response_energy=energy,scaled_direct_curl_energy=curlenergy,
 scaled_source_pairing=reciprocity,curl_energy_error=abs(energy-curlenergy),
 reciprocity_error=abs(energy-reciprocity),max_scaled_curl=maxcurl,
 adaptive_coupling_cell_normalized=2*zscale*zscale*energy,
 full_lift_kkt_residual=reslift,full_source_kkt_residual=ressource,Q_lift_residual=qres,
 physical_normalization='Cell-normalized jet used throughout. No claim that the adaptive profile is physically normalized without transverse multiplicity conversion; positivity is unchanged by its positive scaling.',
 qualification='Floating-point evidence only, no interval enclosures, no full-character exclusion, no cofinal proof.',
 seconds=time.time()-start,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
target=Path(__file__).resolve().parent/f'energy_q2_R26_p{dps}.json'
target.write_text(json.dumps(jsonable(out),indent=2)+'\n')
print('RESULT',target,'c1',mp.nstr(c1,30),'energy',mp.nstr(energy,30),
 'curl_error',mp.nstr(out['curl_energy_error'],8),'reciprocity_error',mp.nstr(out['reciprocity_error'],8),flush=True)
