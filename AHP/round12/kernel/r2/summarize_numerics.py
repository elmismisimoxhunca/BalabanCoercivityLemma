#!/usr/bin/env python3
"""Cross-precision evidence audit; no interval or formal certification."""
from pathlib import Path
import mpmath as mp,json,hashlib
H=Path(__file__).resolve().parent;mp.mp.dps=180
low=json.loads((H/'star_right_q2_R20_p120.json').read_text())
high=json.loads((H/'star_right_q2_R20_p155.json').read_text())
scalar_keys=['root','right_pencil_B_min','negative_scaled_derivative_min_15_angles',
 'charged_prefix_min_15_angles','central_zero_min_15_angles','neutral_min_at_crossing',
 'charged_min_at_pi','central_coordinate_abs']
vector_keys=['charged_low','neutral_spectrum_at_crossing',
 'central_zero_schur_min_at_0_root_halfpi','first_physical_top_jet_sums']
def rel(a,b):
    a,b=mp.mpf(a),mp.mpf(b)
    return abs(a-b)/abs(b) if b else abs(a-b)
differences={k:str(rel(low[k],high[k])) for k in scalar_keys}
differences.update({k:[str(rel(a,b)) for a,b in zip(low[k],high[k])] for k in vector_keys})
# A relative comparison of two roundoff-sized null eigenvalues is meaningless.
differences['charged_nonzero_low']=differences.pop('charged_low')[1:]
null_eigenvalue_abs_difference=str(abs(mp.mpf(low['charged_low'][0])-mp.mpf(high['charged_low'][0])))
checks=[]
for d in (low,high):
    p=d['dps'];eps=mp.power(10,-p+15);jets=list(map(mp.mpf,d['first_physical_top_jet_sums']))
    detect=min(abs(jets[1]),abs(jets[2]))
    entry={'dps':p,'exit':int((H/f'star_right_q2_R20_p{p}.exit').read_text()),
      'correct_case':d['q']==2 and d['R']==20 and d['side']=='right',
      'angle_in_0_halfpi':0<mp.mpf(d['root'])<mp.pi/2,
      'root_null':abs(mp.mpf(d['charged_low'][0]))<eps,
      'charged_gap_positive':mp.mpf(d['charged_low'][1])>0,
      'neutral_spectrum_positive':all(mp.mpf(x)>0 for x in d['neutral_spectrum_at_crossing']),
      'central_zero_positive':all(mp.mpf(x)>0 for x in d['central_zero_schur_min_at_0_root_halfpi']),
      'right_pencil_B_positive':mp.mpf(d['right_pencil_B_min'])>0,
      'right_pencil_P_psd_to_roundoff':mp.mpf(d['right_pencil_P_min'])>=-eps,
      'right_pencil_identity_to_roundoff':mp.mpf(d['right_pencil_max_error'])<eps,
      'sampled_negative_scaled_derivative_positive':mp.mpf(d['negative_scaled_derivative_min_15_angles'])>0,
      'sampled_prefix_positive':mp.mpf(d['charged_prefix_min_15_angles'])>0,
      'sampled_central_zero_positive':mp.mpf(d['central_zero_min_15_angles'])>0,
      'negative_pi_endpoint':mp.mpf(d['charged_min_at_pi'])<0,
      'tangential_jets_nonzero':detect>0,
      'charged_line_scaling_error':d['charged_line_scaling_max_relative_error'],
      'null_residual_over_tangential_jet':str(mp.mpf(d['boundary_null_residual'])/detect),
      'resolvent_residual_over_tangential_jet':str(mp.mpf(d['flat_resolvent_absolute_residual'])/detect),
      'peak_rss_KiB':d['peak_rss_KiB']}
    entry['pass']=entry['exit']==0 and all(v for v in entry.values() if isinstance(v,bool)) and \
      mp.mpf(entry['charged_line_scaling_error'])<mp.mpf('1e-30') and \
      mp.mpf(entry['null_residual_over_tangential_jet'])<mp.mpf('1e-15') and \
      mp.mpf(entry['resolvent_residual_over_tangential_jet'])<mp.mpf('1e-15') and \
      entry['peak_rss_KiB']<2*1024**2
    checks.append(entry)
precision_ok=all(mp.mpf(v)<mp.mpf('1e-20') for v in differences['first_physical_top_jet_sums'][1:]) and \
  mp.mpf(differences['root'])<mp.mpf('1e-80')
paths=[H/'star_crosscheck.py',H/'trial_crosscheck.py',H/'TRIAL_CHECKS.json']
paths += [H/f'star_right_q2_R20_p{p}.{suffix}' for p in (120,155) for suffix in ('json','log','exit')]
result={'case':'right star q=2,R=20; all 64 characters; boundary unit vector',
 'checks':checks,'relative_precision_differences':differences,
 'near_zero_eigenvalue_absolute_difference':null_eigenvalue_abs_difference,
 'precision_comparison_pass':precision_ok,
 'high_precision_values':{k:high[k] for k in scalar_keys+vector_keys+['boundary_null_residual','flat_resolvent_absolute_residual']},
 'artifacts':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths],
 'direct_finite_trial_cases':json.loads((H/'TRIAL_CHECKS.json').read_text())['cases'],
 'qualification':'Finite, non-interval evidence only. Full augmented flat inverse precedes Schur restriction. Schur eigenvalues are NOT full-carrier eigenvalues. Nine-bond boundary normalization is NOT full-carrier normalization. No Lean physical-stencil/DFT identification, uniform positivity bound, cofinal detection, or unconditional premise proof.',
 'pass':all(x['pass'] for x in checks) and precision_ok}
(H/'NUMERICS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['pass'] else 1)
