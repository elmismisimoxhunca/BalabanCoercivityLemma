#!/usr/bin/env python3
"""Full constraint rank, without assuming that a zero-sector inverse suffices.
QfullOf: ZXR2Sector.lean:97; raw formula anchors in SOURCES.md.
Select fine bond (y+e_mu,mu) for each top coarse bond (y,mu).
At eps=0 this minor is (1/8) I. Check strict ROW diagonal dominance
in the UNWRAPPED lattice, before characters can cause cancellations.
Q0 uses disjoint identity columns, so this proves numerical full row rank
in every character. Local row patterns do not depend on q,R once separated.
This is arbitrary-precision evidence, not an interval or Lean proof.
"""
import sys
sys.dont_write_bytecode = True
from probe import *

def check(eps,dps):
    mp.mp.dps=dps;f=Family(1,18,mp.mpf(eps));worst=mp.inf;curved=0;rows=[]
    for b in f.b1:
        base,legs=f.rawdata[b];used=set(base)
        for l,m,r in legs:used.update(l+m+r)
        coeff={};iscurved=any(f.angle(e) for e in used)
        if iscurved:
            curved+=1
            for e in used:coeff[e]=f.rawjet(b,{e:1})[1]
        else:
            for l,m,r in legs:
                for e in m:coeff[e]=coeff.get(e,0)+mp.mpf(1)/16
        chosen={}
        for (x,mu),c in coeff.items():
            if all(x[j]%2==int(j==mu) for j in range(3)):
                y=f.shift(x,mu,-1)
                # A coarse touching top bond, at stride two.
                if f.in1(y) or f.in1(f.shift(y,mu,2)):
                    chosen[(y,mu)]=chosen.get((y,mu),0)+c
        diagonal=abs(chosen.get(b,0));off=sum(abs(c) for e,c in chosen.items() if e!=b)
        margin=diagonal-off;worst=min(worst,margin)
        if iscurved:rows.append(dict(base=b,diagonal=diagonal,offsum=off,margin=margin))
    assert worst>mp.mpf('.12')
    return dict(epsilon=eps,dps=dps,minimum_diagonal_dominance_margin=worst,curved_rows=curved,rows=rows)
if __name__=='__main__':
    ans=[check(e,p) for p in [70,100] for e in ['1e-3','1e-4','1e-5','1e-6','1e-18','1e-25','1e-40']]
    (OUT/'rank_check.json').write_text(json.dumps(jsonable(ans),indent=2)+'\n')
    print(json.dumps(jsonable(ans),indent=2))
