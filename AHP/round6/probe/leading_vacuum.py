#!/usr/bin/env python3
"""Finite-sum coefficient c1(q,R) at the exact numerical VACUUM crossing.
This is different from extrapolating eps=1e-6. No positivity theorem is claimed.
The sum is 2 sum leading_h[j] C2^0_j(W0 v0); all operator anchors SOURCES.md.
"""
import sys
sys.dont_write_bytecode = True
from leading_source import *
mp.mp.dps=340;f=Family(2,18,mp.mpf(0),7,7,1).assemble();S=f.boundary_inverse()
def low(t):return mp.eighe(S+f.theta(t),eigvals_only=True)[0]
t=mp.findroot(low,(mp.mpf('.5'),mp.mpf('.6')),tol=mp.mpf('1e-320'),verify=False)
ev,V=mp.eighe(S+f.theta(t));rhs=S*V[:,0]
x=[sum(f.X[k][i]*rhs[k] for k in range(len(f.X))) for i in range(f.aug.n)]
norm=mp.sqrt(sum(abs(z)**2 for z in x[:f.n]));x=[z/norm for z in x]
w=f.dressed(x[:f.n],x[f.n:f.n+f.H.n]);h=leading_h(f)
c,terms=f.correction(w,h)
ref=json.loads((OUT/'q2_R18_e1e-6_p400_s7_7.json').read_text())
row=dict(q=2,R=18,dps=340,sector=[7,7],vacuum_root=t,vacuum_second_schur_eigenvalue=ev[1],
    finite_sum_c1=c,ratio_to_e1e6_extrapolation=mp.mpf(ref['pairing'])/mp.mpf('1e-6')/c,
    positive_terms=sum(max(z,0) for z in terms),negative_terms=sum(min(z,0) for z in terms))
(OUT/'leading_vacuum.json').write_text(json.dumps(jsonable(row),indent=2)+'\n');print(json.dumps(jsonable(row),indent=2))
