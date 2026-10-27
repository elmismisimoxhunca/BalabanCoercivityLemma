#!/usr/bin/env python3
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=300
D=Path(__file__).resolve().parent
load=lambda name:json.loads((D/name).read_text())
fmt=lambda x:mp.nstr(x,12)
a=load('precise_q2_R32_s7_7_c1_p190.json');b=load('precise_q2_R32_s7_7_c1_p230.json')
left={'case':'left twist q=2 R=32 charge=1 character=(7,7)',
 'root_absolute_190_230_difference':fmt(abs(mp.mpf(a['root'])-mp.mpf(b['root']))),
 'relative_190_230_differences':{k:fmt(abs(mp.mpf(a[k])/mp.mpf(b[k])-1)) for k in ['canonical_coupling','first_tangential_jet','kernel_form_slope']},
 'root':fmt(mp.mpf(b['root'])),'next_schur_eigenvalue':fmt(mp.mpf(b['schur_low'][1])),
 'canonical_coupling':fmt(mp.mpf(b['canonical_coupling'])),
 'first_tangential_jet':fmt(mp.mpf(b['first_tangential_jet'])),
 'kernel_form_slope':fmt(mp.mpf(b['kernel_form_slope'])),
 'residual_over_coupling':fmt(mp.mpf(b['residual_over_coupling'])),
 'color_gram_anisotropy':fmt(mp.mpf(b['full_torus_color_anisotropy']))}
competitors=[]
for name in ['precise_q2_R32_s0_0_c1_p80.json','precise_q2_R32_s1_1_c1_p80.json','precise_q2_R32_s0_0_c0_p80.json']:
    x=load(name)
    competitors.append({'file':name,'min_schur_eigenvalue':fmt(mp.mpf(x['schur_low'][0])),'reconstructed_vector_A_norm_not_solver_error':fmt(mp.mpf(x['augmented_residual'])), 'theta_trig_identity_error':fmt(mp.mpf(x['pencil_error']))})
stars=[]
for side in ['left','right']:
    def fname(d):
      p=D/f'star_{side}_q1_R20_p{d}.json'
      if side=='left' and not p.exists():p=D/f'star_q1_R20_p{d}.json'
      return p
    p90,p120=fname(90),fname(120)
    if not (p90.exists() and p120.exists()):continue
    aa=json.loads(p90.read_text());bb=json.loads(p120.read_text())
    stars.append({'case':f'{side} star q=1 R=20',
      'root_absolute_90_120_difference':fmt(abs(mp.mpf(aa['root'])-mp.mpf(bb['root']))),
      'relative_90_120_top_jet_sum_differences':[fmt(abs(mp.mpf(x)/mp.mpf(y)-1)) for x,y in zip(aa['first_physical_top_jet_sums'],bb['first_physical_top_jet_sums'])],
      'root':fmt(mp.mpf(bb['root'])),'next_schur_eigenvalue':fmt(mp.mpf(bb['charged_low'][1])),
      'neutral_min_at_crossing':fmt(mp.mpf(bb['neutral_min_at_crossing'])),
      'central_zero_schur_min_at_0_root_halfpi':[fmt(mp.mpf(x)) for x in bb['central_zero_schur_min_at_0_root_halfpi']],
      'top_jet_sums':[fmt(mp.mpf(x)) for x in bb['first_physical_top_jet_sums']],
      'residual':fmt(mp.mpf(bb['flat_resolvent_absolute_residual'])),
      'boundary_null_residual':fmt(mp.mpf(bb['boundary_null_residual'])),
      'central_coordinate_abs':fmt(mp.mpf(bb['central_coordinate_abs']))})
result={'left_twist':left,'competitors':competitors,'finite_stars':stars,
 'qualification':'All spectra are boundary Schur spectra, not full-carrier eigenvalues. No interval certificate, frozen-operator Fourier identification, cofinal proof, or proved premise.'}
(D/'NUMERICS_SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
