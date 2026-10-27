#!/usr/bin/env python3
"""Closed leading neutral source multiplier. Operators: SOURCES.md.
At eps=0, the neutral transverse-uniform constrained tangential field is
(alpha_j,-alpha_j) on each two-site block. Curl energy gives diag 6/offdiag 1.
The projected defect source gives rhs (3/2)e_0. With n=4q(R+1),
alpha_j=(-1)^j*(3/2)*sinh((n-j)gamma)/sinh((n+1)gamma), cosh gamma=3.
Then (H*J)' on direction 1 is delta_(j,0)-2*alpha_(j-1)+2*alpha_(j+1),
with zero exterior alpha. Other top directions have zero first coefficient.
"""
import sys
sys.dont_write_bytecode = True
from probe import *

def leading_h(f):
    n=(f.s-f.p)//2;gamma=mp.acosh(3)
    alpha=[mp.mpf(3)/2*(-1)**j*mp.sinh((n-j)*gamma)/mp.sinh((n+1)*gamma) for j in range(n)]
    ans=[mp.mpf(0)]*len(f.b1)
    for j in range(n):ans[3*j+2]=int(j==0)-2*(alpha[j-1] if j else 0)+2*(alpha[j+1] if j+1<n else 0)
    return ans
if __name__=='__main__':
    mp.mp.dps=320;rows=[]
    for q,R in [(1,18),(2,18),(2,30)]:
        eps=mp.mpf('1e-12');f=Family(q,R,eps,charge=0).assemble();h,res=f.hj();lin=leading_h(f)
        maxerr=max(abs(a/eps-b) for a,b in zip(h,lin));tailerr=abs(h[-2]/eps/lin[-2]-1)
        rows.append(dict(q=q,R=R,epsilon='1e-12',dps=320,max_first_coefficient_error=maxerr,
            last_nonzero_relative_error=tailerr,solve_residual=res,first_coefficient=lin[2],last_coefficient=lin[-2]))
    (OUT/'leading_source.json').write_text(json.dumps(jsonable(rows),indent=2)+'\n')
    print(json.dumps(jsonable(rows),indent=2))
