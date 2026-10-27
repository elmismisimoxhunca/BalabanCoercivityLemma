#!/usr/bin/env python3
"""Audit all requested samples from actual JSON, not logs or expectations."""
import sys
sys.dont_write_bytecode=True
import csv,json,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=400
P=Path(__file__).resolve().parent
rho=(3-mp.sqrt(5))/2
tinf=mp.acos((-1+mp.sqrt(193+32*rho))/16)
def num(x):return mp.mpf(x)
def s(x,n=25):return mp.nstr(x,n)
def digits(a,b):
    err=abs(num(a)-num(b))/max(abs(num(b)),mp.mpf('1e-350'))
    return float(-mp.log10(err)) if err else 999.
rows=[];spectra=[];initials=[]
for q in [1,2]:
 for R in [18,20,24,30]:
  for eps in ['1e-3','1e-4','1e-5','1e-6']:
   sector='0_0' if q==1 else '7_7'
   files=list(P.glob(f'q{q}_R{R}_e{eps}_p*_s{sector}.json'))
   runs=sorted([json.loads(f.read_text()) for f in files],key=lambda x:x['dps'])
   assert len(runs)>=2
   low,hi=runs[0],runs[-1];pair=num(hi['pairing']);assert pair>0
   assert num(hi['alternative_offset'])>0
   assert num(hi['alternative_carrier_test_form'])>0
   assert num(hi['alternative_corrected_test_form'])<0
   assert num(hi['alternative_boundary_schur_min'])>0
   assert num(hi['schur_eigenvalues'][1])>0
   completed=[json.loads(f.read_text()) for f in P.glob(f'sectors_q{q}_R{R}_e{eps}*.json') if json.loads(f.read_text()).get('complete')]
   assert completed
   screen=max(completed,key=lambda a:a['assembly_dps']);assert len(screen['sectors'])==2*(4*q)**2
   if q==1:
    others=[a for a in screen['sectors'] if not(a['charge']==1 and a['character']==[0,0])]
    gap=min(a['at_first_zero_sector_crossing_schur_min'] for a in others)
   else:
    actual=next(a for a in json.loads((P/'actual_sector_audit.json').read_text()) if a['R']==R and a['epsilon']==eps)
    gap=min(a['schur_min_at_first_root'] for a in actual['checked'])
    others=[a for a in screen['sectors'] if a['at_first_zero_sector_crossing_schur_min']>1e-10]
    oldgap=min(a['at_first_zero_sector_crossing_schur_min'] for a in others)*float(mp.sin(num(hi['root']))/mp.sin(num(screen['root'])))
    gap=min(gap,oldgap)
   assert gap>0
   for a in screen['sectors']:
    assert a['initial_boundary_schur_min']>0 and a['pre_crossing_grid_min']>0
    assert a['B_inertia']['positive']==a['B_minus_D_inertia']['positive']
    assert a['B_inertia']['negative']==a['B_minus_D_inertia']['negative']
   ip=P/f'initial_q{q}_R{R}_e{eps}_p70_s0_0.json';ini=json.loads(ip.read_text())
   for k,v in ini['required_augmented_inertia'].items():
    assert ini['B_inertia'][k]==ini['B_minus_D_inertia'][k]==v
   assert ini['B_min_double']>0 and ini['B_minus_D_min_double']>0
   row=dict(q=q,R=R,epsilon=eps,first_character=[0,0] if q==1 else [7,7],precisions=[a['dps'] for a in runs],
    pairing=s(pair),pairing_relative_digits_low_to_high=digits(low['pairing'],hi['pairing']),
    pairing_relative_digits_second_high_to_high=digits(runs[-2]['pairing'],hi['pairing']),
    coefficient_over_eps2_rho4qR=s(pair/num(eps)**2/rho**(4*q*R)) if q==1 else None,
    coefficient_over_eps=s(pair/num(eps)) if q==2 else None,
    root=s(num(hi['root']),80),root_minus_t_infinity=s(num(hi['root'])-tinf),
    second_schur_eigenvalue=s(num(hi['schur_eigenvalues'][1])),
    residual=s(num(hi['augmented_kernel_max_residual'])),
    residual_over_pairing=s(num(hi['augmented_kernel_max_residual'])/pair),
    alternate_offset=s(num(hi['alternative_offset'])),
    alternate_A_test=s(num(hi['alternative_carrier_test_form'])),
    alternate_F_test=s(num(hi['alternative_corrected_test_form'])),
    alternate_boundary_gap=s(num(hi['alternative_boundary_schur_min'])),
    other_sector_gap_double=gap,initial_B_gap_double=ini['B_min_double'],
    initial_B_minus_D_gap_double=ini['B_minus_D_min_double'],initial_min_pivot=s(num(ini['B_minus_D_inertia']['min_abs_pivot'])),
    screen_dps=screen['assembly_dps'])
   rows.append(row);spectra+=screen['sectors'];initials.append(ini)
small=[]
for eps in ['1e-18','1e-25','1e-40']:
 runs=sorted([json.loads(f.read_text()) for f in P.glob(f'q1_R18_e{eps}_p*_s0_0.json')],key=lambda a:a['dps'])
 lo,hi=runs[0],runs[-1]
 small.append(dict(epsilon=eps,pairing=hi['pairing'],left_half_mass=hi['left_half_mass'],
  coefficient_over_eps2_rho72=s(num(hi['pairing'])/num(eps)**2/rho**72),
  stable_relative_digits=digits(lo['pairing'],hi['pairing']),second_schur_eigenvalue=hi['schur_eigenvalues'][1]))
negative_low=json.loads((P/'q2_R18_e1e-100_p400_s7_7.json').read_text())
negative_high=json.loads((P/'q2_R18_e1e-100_p500_s7_7.json').read_text())
assert num(negative_high['pairing'])<0
negative=dict(q=2,R=18,epsilon='1e-100',character=[7,7],precisions=[400,500],
 pairing=s(num(negative_high['pairing']),50),
 stable_relative_digits=digits(negative_low['pairing'],negative_high['pairing']),
 left_half_mass=s(num(negative_high['left_half_mass'])),
 root=s(num(negative_high['root']),100),
 residual_over_abs_pairing=s(num(negative_high['augmented_kernel_max_residual'])/abs(num(negative_high['pairing']))),
 alternative_carrier_test=s(num(negative_high['alternative_carrier_test_form'])),
 alternative_corrected_test=s(num(negative_high['alternative_corrected_test_form'])),
 alternative_schur_gap=s(num(negative_high['alternative_boundary_schur_min'])),
 vacuum_leading_coefficient=json.loads((P/'leading_vacuum.json').read_text())['finite_sum_c1'])
summary=dict(verdict='negative-at-arbitrarily-small-amplitude-regime: unchanged all-q first-crossing family fails numerically',
 negative_first_crossing=negative,requested_samples=len(rows),all_requested_pairings_positive=True,
 all_requested_alternative_test_forms_negative=True,full_sector_screens=len(spectra),
 minimum_stable_pairing_digits=min(r['pairing_relative_digits_low_to_high'] for r in rows),
 caveat='q2 zero-character artifacts are provisional non-first crossings, NOT guarded alternative witnesses',
 minimum_other_sector_schur_gap_double=min(r['other_sector_gap_double'] for r in rows),
 minimum_initial_B_minus_D_gap_double=min(r['initial_B_minus_D_gap_double'] for r in rows),
 maximum_initial_B_minus_D_gap_double=max(r['initial_B_minus_D_gap_double'] for r in rows),
 maximum_residual_over_pairing=s(max(num(r['residual_over_pairing']) for r in rows)),
 rho=s(rho,80),t_infinity=s(tinf,100),decay_per_qR=s(-4*mp.log(rho)),
 minimum_pairing=min(rows,key=lambda r:num(r['pairing']))['pairing'],
 max_peak_rss_KiB=max(json.loads(p.read_text()).get('peak_rss_KiB',0) for p in P.glob('*.json') if isinstance(json.loads(p.read_text()),dict)),
 tiny_amplitudes=small,rows=rows)
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
with (P/'TABLE.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(P.iterdir()) if p.is_file() and p.name not in ['MANIFEST.json','summary.log','summary.exit']}
(P/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['rows','tiny_amplitudes']},indent=2))
print('TINY',json.dumps(small,indent=2))
for r in rows:
 if r['epsilon']=='1e-6':print(r['q'],r['R'],r['pairing'],r['coefficient_over_eps2_rho4qR'],r['coefficient_over_eps'],r['other_sector_gap_double'])
