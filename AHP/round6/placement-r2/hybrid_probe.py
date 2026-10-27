#!/usr/bin/env python3
"""Hybrid placement probe, NOT a first-crossing or formal sign certificate.

Verbatim numerical primitives are imported read-only from ../probe/probe.py.
All their Lean file/line citations are in ../probe/SOURCES.md (copied into
this directory's SOURCES.md). New mask: Attempt.lean hybridMask/hybridU:
boundary direction-1 defect at 4*q+2, original core at (2*R+4)*q,
transverse coordinates even. Boundary amplitude = bsign*eps; core = csign*eps.
No other operator or normalization is changed. Only the selected charged
character is evaluated; NO complementary-sector unit is inferred.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'probe'))
import probe as p
import argparse,json

Base=p.Family
class Hybrid(Base):
    bsign=1
    csign=-1
    def angle(self,b,t=0):
        x,d=b
        if not (self.in0(x) or self.in0(self.shift(x,d))): return t
        if x[1]%2==0 and x[2]%2==0 and d==1:
            if x[0]==self.lo+2: return self.bsign*self.eps
            if x[0]==self.p: return self.csign*self.eps
        return 0

if __name__=='__main__':
    a=argparse.ArgumentParser()
    for name,default in [('q',1),('R',18),('dps',100),('iy',0),('iz',0),('bsign',1),('csign',-1)]:
        a.add_argument('--'+name,type=int,default=default)
    a.add_argument('--eps',default='1e-3')
    args=a.parse_args()
    Hybrid.bsign=args.bsign;Hybrid.csign=args.csign
    p.Family=Hybrid
    p.OUT=HERE/f'b{args.bsign}_c{args.csign}'
    p.OUT.mkdir(exist_ok=True)
    d=p.run(args.q,args.R,args.eps,args.dps,args.iy,args.iz)
    d.update(boundary_sign=args.bsign,core_sign=args.csign,
        family='hybrid: boundary 4q+2 and original core (2R+4)q',
        first_crossing_status='NOT CHECKED: only the selected charged character was computed',
        kernel_real_dimension_in_this_sector='not certified: numerical eigenvalues only',
        dictionary='../SOURCES.md')
    path=p.OUT/f'q{args.q}_R{args.R}_e{args.eps}_p{args.dps}_s{args.iy}_{args.iz}.json'
    path.write_text(json.dumps(p.jsonable(d),indent=2)+'\n')
