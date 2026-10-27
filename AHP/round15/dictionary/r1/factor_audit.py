#!/usr/bin/env python3
"""Audit exact collar mode factors and the right-star dominant rate. Evidence only."""
from pathlib import Path
import json,math
import numpy as np
import mpmath as mp

H=Path(__file__).resolve().parent
ROOT=H.parents[3]
mp.mp.dps=160

def z(s):return complex(s.replace(' ','').strip('()'))
def companion(d):
    def mat(name):return np.array([[z(v) for v in row] for row in d['reduced_blocks'][name]])
    A,B,C=mat('A'),mat('B'),mat('C')
    return np.block([[-np.linalg.solve(A,B),-np.linalg.solve(A,C)],[np.eye(8),np.zeros((8,8))]])
def polymul(a,b):return np.polynomial.polynomial.polymul(a,b)
def factors_for(iy,iz):
    if (iy%2,iz%2)==(0,0):
        if iy==0 and iz==0:return [(11,2),(7,4),(3,2)]
        if iy==2 and iz==2:return [(7,8)]
        return [(9,4),(5,4)]
    if (iy==0 and iz%2==1) or (iy%2==1 and iz==0):
        return [(5-mp.sqrt(2),2),(5+mp.sqrt(2),2),(9-mp.sqrt(2),2),(9+mp.sqrt(2),2)]
    if (iy%2,iz%2)==(1,1):
        return [(7-2*mp.sqrt(2),2),(7,4),(7+2*mp.sqrt(2),2)]
    return [(7-mp.sqrt(2),4),(7+mp.sqrt(2),4)]

def candidate(fs):
    p=np.array([1.0+0j])
    for y,m in fs:
        q=np.array([1+0j,-complex(y),1+0j])
        for _ in range(m):p=polymul(p,q)
    return p

records=[]
for iy in range(4):
    for iz in range(4):
        d=json.loads((H/f'full_q1_R20_c{iy}_{iz}_x220.json').read_text())
        T=companion(d); actual=np.poly(T); expected=candidate(factors_for(iy,iz))
        scale=max(1.0,float(np.max(np.abs(expected))))
        records.append({'character':[iy,iz],
          'factor_y_multiplicities':[(str(y),m) for y,m in factors_for(iy,iz)],
          'charpoly_max_abs_error':float(np.max(np.abs(actual-expected))),
          'charpoly_relative_error':float(np.max(np.abs(actual-expected))/scale),
          'transfer_determinant_error':float(abs(np.linalg.det(T)-1)),
          'max_root_modulus':float(max(abs(np.linalg.eigvals(T))))})

# The dominant class has y=5-sqrt(2); solve lambda+lambda^-1=y explicitly.
y=5-mp.sqrt(2)
rho=(y+mp.sqrt(y*y-4))/2
rho_inv=(y-mp.sqrt(y*y-4))/2
D={20:json.loads((ROOT/'AHP/round12/kernel/r1/star_right_q1_R20_p120.json').read_text())}
for R in (22,24,26,28):D[R]=json.loads((ROOT/f'AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json').read_text())
for R in (30,32):
    for p in (120,155):
        D[(R,p)]=json.loads((ROOT/f'AHP/round14/assembly/r2/star_right_q1_R{R}_p{p}.json').read_text())
area=[]
for R in (20,22,24,26,28):
    a=mp.mpf(D[R]['first_physical_top_jet_sums'][1])
    area.append({'R':R,'area':str(a),'normalized_areaSum':str(2*a*rho**(4*R)),
      'rate_if_previous':str(a/mp.mpf(D[R-2]['first_physical_top_jet_sums'][1])) if R>20 else None,
      'rate_times_rho8':str(a/mp.mpf(D[R-2]['first_physical_top_jet_sums'][1])*rho**8) if R>20 else None})
for R in (30,32):
    a=mp.mpf(D[(R,155)]['first_physical_top_jet_sums'][1])
    prevdata=D[(R-2,155)] if R==32 else D[28]
    prev=mp.mpf(prevdata['first_physical_top_jet_sums'][1])
    area.append({'R':R,'area':str(a),'normalized_areaSum':str(2*a*rho**(4*R)),
      'rate_if_previous':str(a/prev),'rate_times_rho8':str(a/prev*rho**8)})
result={'qualification':'Non-interval numerical evidence only. Exact algebraic formulas are audited against the numerical frozen-family matrices; no Lean physical identification is asserted.',
  'records':records,'dominant':{'y':str(y),'rho':str(rho),'rho_inverse':str(rho_inv),
    'product_error':str(rho*rho_inv-1),'rho8':str(rho**8),'area_progression':area},
  'pass':all(r['charpoly_relative_error']<1e-7 and r['transfer_determinant_error']<1e-7 for r in records)}
(H/'FACTOR_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':result['pass'],'worst_charpoly_relative_error':max(r['charpoly_relative_error'] for r in records),
  'dominant':result['dominant']},indent=2))
raise SystemExit(0 if result['pass'] else 1)
