#!/usr/bin/env python3
"""Identify the actual q=2 first sector, without rerunning all 128 inverses.
The completed all-sector screens used the later zero-character crossing.
Only (0,0),(0,7),(7,0),(7,7) were nonpositive there. At the (7,7)
root check the other three directly. The trig identity from path_identity.py
and positivity of B imply positivity earlier for every already-positive
sector. All new Schur spectral checks here are DOUBLE, labelled as such.
"""
import sys
sys.dont_write_bytecode = True
from sectors import *
mp.mp.dps=80;rows=json.loads((OUT/'actual_sector_audit.json').read_text()) if (OUT/'actual_sector_audit.json').exists() else []
for R in [18,20,24,30]:
 for eps in ['1e-3','1e-4','1e-5','1e-6']+(['1e-100'] if R==18 else []):
  if any(r['R']==R and r['epsilon']==eps for r in rows):continue
  primary=max((json.loads(p.read_text()) for p in OUT.glob(f'q2_R{R}_e{eps}_p*_s7_7.json')),key=lambda p:p['dps'])
  screens=[json.loads(p.read_text()) for p in OUT.glob(f'sectors_q2_R{R}_e{eps}*.json') if json.loads(p.read_text()).get('complete')]
  screen=max(screens,key=lambda a:a['assembly_dps'])
  bad=[s for s in screen['sectors'] if s['at_first_zero_sector_crossing_schur_min']<=0]
  assert all(s['charge']==1 and s['character'] in [[0,0],[0,7],[7,0],[7,7]] for s in bad)
  result=dict(q=2,R=R,epsilon=eps,first_character=[7,7],first_root=primary['root'],
      method='mp-assembled, double Schur spectra plus exterior trig monotonicity',checked=[])
  for iy,iz in [(0,0),(0,7),(7,0)]:
   f=Family(2,R,mp.mpf(eps),iy,iz,1).assemble();lu=splu(f.aug.scipy())
   rhs=np.zeros((f.aug.n,len(f.boundary)),complex);rhs[f.boundary,np.arange(len(f.boundary))]=1
   X=lu.solve(rhs);C=X[f.boundary];S=np.linalg.inv(C);S=(S+S.conj().T)/2
   eig=eigvalsh(S+np.array(f.theta(mp.mpf(primary['root'])).tolist(),complex))
   gap=float(eig[0]);assert gap>0
   result['checked'].append(dict(character=[iy,iz],schur_min_at_first_root=gap))
  rows.append(result)
  (OUT/'actual_sector_audit.json').write_text(json.dumps(rows,indent=2)+'\n')
  print('ACTUAL',R,eps,result['checked'],flush=True)
