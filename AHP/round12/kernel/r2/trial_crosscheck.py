#!/usr/bin/env python3
"""Independent physical right-star finite-support trials, no inverse/Schur energy.
Evidence only: local stencil has no machine-checked frozen-operator identification.
"""
import os,sys,resource
os.environ['OPENBLAS_NUM_THREADS']='1'; os.environ['OMP_NUM_THREADS']='1'
sys.dont_write_bytecode=True
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
from pathlib import Path
import mpmath as mp,json
mp.mp.dps=130
OUT=Path(__file__).resolve().parent

def shift(x,d,step=1):
    y=list(x); y[d]+=step;return tuple(y)
def boundary(p):
    x,mu,nu=p
    return [(x,mu),(shift(x,mu),nu),(shift(x,nu),mu),(x,nu)]
def touched(b):
    x,mu=b; ans=[]
    for nu in range(3):
        if nu==mu:continue
        a,c=sorted((mu,nu))
        ans.extend([(x,a,c),(shift(x,nu,-1),a,c)])
    return ans

def run(q,R):
    x=(q*(12*R+12)-1,0,0)
    star={(shift(x,d,sgn),0,d) for d in (1,2) for sgn in (0,-1)}
    results=[]
    for b in (mp.mpf(0),mp.mpf(1)/4):
        field={(x,0):mp.mpf(1)}
        for d in (1,2):
            for s in (-1,1):field[(shift(x,d,s),0)]=-s*mp.j/4
        if b: field[(x,1)]=-mp.j*b
        plaques=set().union(*(set(touched(e)) for e in field))
        mass=sum(abs(z)**2 for z in field.values())
        unaffected=mp.mpf(0); affected=mp.mpf(0)
        for p in plaques:
            vals=[field.get(e,mp.mpf(0)) for e in boundary(p)]
            if p in star:
                # Frozen atom order [2,3,0,1], signs [-,-,+,+].
                # At the right star the exterior atom4 is exactly zero.
                atoms=[-vals[2],-vals[3],vals[0],vals[1]]
                assert atoms[3]==0
                value=2*sum(mp.im(mp.conj(atoms[i])*atoms[j])
                  for i in range(4) for j in range(i+1,4))
                affected+=value
            else:unaffected+=abs(vals[0]+vals[1]-vals[2]-vals[3])**2
        # Check all trial coordinates are genuine level-zero collar bonds.
        corelo=q*(2*R+4); corehi=q*(10*R+12)
        endpoints=[y for e in field for y in (e[0],shift(e[0],e[1]))]
        assert all(not(corelo<=y[0]<corehi) for y in endpoints)
        energy=mass+unaffected+affected
        expect=-mp.mpf(1)/4 if b else 0
        assert abs(energy-expect)<mp.mpf('1e-120')
        results.append(dict(tangent_amplitude=str(b),mass=str(mass),
          untwisted_plaquette_energy=str(unaffected),star_plaquette_energy=str(affected),
          total_energy=str(energy),expected=str(expect),
          support_bonds=len(field),plaquettes=len(plaques),all_endpoints_off_omega1=True))
    return dict(q=q,R=R,side='right',dps=mp.mp.dps,tests=results)
result={'cases':[run(2,20),run(4,22),run(8,24)],
 'qualification':'Independent direct finite-support physical stencil evidence; no Schur complement or reduced inverse. W=id,T=0 and level-zero masses have separate generic Lean locality lemmas, but finite plaquette enumeration and its frozen-operator join remain unproved.',
 'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(OUT/'TRIAL_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
