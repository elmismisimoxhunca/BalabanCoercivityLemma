#!/usr/bin/env python3
"""Check the exact exterior trig reduction, not a sampling argument for IVT.
The plaquette formulas are DeltaPrimeOperator.lean:287-395 and ZLocOps.lean:119,186;
Uth is D1Path.lean:46. The identity follows by substituting diagonal Uth:
Theta(t)=cos(t)*Theta(0)+sin(t)*Theta(pi/2). This script numerically checks
all sampled characters; the pencil consequence is explained in PROBE.md.
"""
import sys
sys.dont_write_bytecode = True
from probe import *
mp.mp.dps=80;report=[]
for q in [1,2]:
    for charge in [0,1]:
        for iy,iz in itertools.product(range(4*q),repeat=2):
            f=Family(q,2,mp.mpf('1e-3'),iy,iz,charge)
            out,_=f.plaq('out',0)
            f.boundary=sorted({f.em[j] for i,row in enumerate(out.r) for j in row if j in f.em and i in f.em})
            a=f.theta(0);b=f.theta(mp.pi/2);errors=[]
            for t in [mp.mpf('.1'),mp.mpf('.3'),mp.mpf('.586'),mp.mpf('.9'),mp.mpf('2.1')]:
                errors.append(mp.norm(f.theta(t)-mp.cos(t)*a-mp.sin(t)*b,'inf'))
            er=max(errors);assert er<mp.mpf('1e-75')
            report.append(dict(q=q,charge=charge,character=[iy,iz],max_error=er))
(OUT/'path_identity.json').write_text(json.dumps(jsonable(report),indent=2)+'\n')
print('160 sectors, max entry-row norm error',fmt(max(x['max_error'] for x in report)))
