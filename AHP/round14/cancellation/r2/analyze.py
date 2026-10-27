#!/usr/bin/env python3
"""Audit the row-profile and leading-orientation numerical diagnostics."""
from pathlib import Path
import json,re,hashlib
from decimal import Decimal,getcontext
import numpy as np
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[3]
getcontext().prec=60

def load(path): return json.loads(Path(path).read_text())
def C(x): return complex(x.strip('()').replace(' ',''))
def sha(path):
 p=Path(path); return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None

first=OUT/'row_profile_right_q1_R20_p40.log'
tail=OUT/'row_profile_right_q1_R20_p40_tail72.json'
rows={}
for m in re.finditer(r'^ROW (\d+) x (\d+) area (\S+) seconds',first.read_text(),re.M):
 j,x,a=int(m.group(1)),int(m.group(2)),m.group(3)
 rows[j]={'j':j,'x':x,'areaSum_direct':a,'source':'partial log'}
for item in load(tail)['profile']:
 rows[item['j']]={'j':item['j'],'x':item['x'],
   'areaSum_direct':item['areaSum_direct'],'source':'exit-0 tail JSON'}
assert set(rows)==set(range(84)),(len(rows),sorted(set(range(84))-set(rows)))
assert all(rows[j]['x']==44+2*j for j in rows)
assert all(Decimal(rows[j]['areaSum_direct'])>0 for j in rows)
ref=load(ROOT/'AHP/round14/cancellation/r1/structure_right_q1_R20_p50.json')
last=Decimal(rows[83]['areaSum_direct']); expected=Decimal(ref['areaSum_from_Hermitian'])
assert abs(last-expected)/expected<Decimal('1e-20')
early80=load(OUT/'row_profile_right_q1_R20_p80_early80.json')
early_errors={}
for item in early80['profile']:
 j=item['j']; a=Decimal(item['areaSum_direct']); b=Decimal(rows[j]['areaSum_direct'])
 assert a>0
 early_errors[str(j)]=str(abs(a-b)/max(abs(a),abs(b)))

areas={20:expected}
for R in [22,24,26,28]:
 d=load(ROOT/f'AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json')
 areas[R]=2*Decimal(d['first_physical_top_jet_sums'][1])
d=load(ROOT/'AHP/round14/assembly/r2/star_right_q1_R30_p120.json')
areas[30]=2*Decimal(d['first_physical_top_jet_sums'][1])
ratios={str(R):str(areas[R-2]/areas[R]) for R in [22,24,26,28,30]}
kappa=areas[28]/areas[30]
normalized={str(R):str(areas[R]*kappa**(Decimal(R)/2)) for R in areas}

orient={}
for R,path in [(20,ROOT/'AHP/round14/cancellation/r1/structure_right_q1_R20_p50.json'),
               (22,OUT/'structure_right_q1_R22_p40.json')]:
 D=load(path)
 K=np.array([[C(x).real for x in row] for row in D['K']]);z=np.array([C(x) for x in D['z']])
 pairs=[[0],[1,5],[2,6],[3,7],[4,8]];B=np.zeros((9,5))
 for j,inds in enumerate(pairs):
  for i in inds:B[i,j]=1/np.sqrt(len(inds))
 Ks=B.T@K@B;zs=B.T@z;w,V=np.linalg.eigh(1j*Ks)
 contrib=w*np.abs(V.conjugate().T@zs)**2
 orient[str(R)]={'hermitian_eigenvalues':[float(x) for x in w],
   'eigen_contributions':[float(x) for x in contrib],
   'sum_contributions':float(sum(contrib)),
   'boundary_vector_norm_squared':float(np.vdot(zs,zs).real),
   'dominant_negative_contribution':float(min(contrib)),
   'dominant_positive_contribution':float(max(contrib))}

result={'qualification':'Non-interval numerical evidence only; not a Lean proof or a recurrence certificate.',
 'row_profile':{'q':1,'R':20,'row_count':len(rows),'positive_rows':sum(Decimal(rows[j]['areaSum_direct'])>0 for j in rows),
   'all_rows_positive':True,'rows':[rows[j] for j in sorted(rows)],
   'partial_log_timeout_after_row':74,'tail_exit':(OUT/'row_profile_right_q1_R20_p40_tail72.exit').read_text().strip(),
   'last_row_matches_round1_hermitian':True,
   'early_precision_check':{'dps':80,'rows':len(early_errors),'relative_errors':early_errors,
     'max_relative_error':max(early_errors.values(),key=Decimal),
     'exit':(OUT/'row_profile_right_q1_R20_p80_early80.exit').read_text().strip()}},
 'radius_dominant_fit':{'areaSum':{str(R):str(areas[R]) for R in areas},
   'successive_ratios':ratios,'kappa_R28_to_R30':str(kappa),'normalized_by_kappa_pow_R_over_2':normalized,
   'warning':'This is a stable one-rate fit, not an exact matrix limit or a proof of the leading coefficient.'},
 'symmetric_boundary_orientation':orient,
 'inputs':{str(p):sha(p) for p in [first,tail,ROOT/'AHP/round14/cancellation/r1/structure_right_q1_R20_p50.json',
   OUT/'structure_right_q1_R22_p40.json',OUT/'row_profile_right_q1_R20_p80_early80.json']}}
(OUT/'PROFILE_ANALYSIS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['row_profile','symmetric_boundary_orientation']},indent=2))
print('rows',len(rows),'all positive',result['row_profile']['all_rows_positive'])
for R in sorted(orient): print('R',R,'orientation',orient[R])
