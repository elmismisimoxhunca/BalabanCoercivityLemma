#!/usr/bin/env python3
"""Final read-only data/source checks, writing only this track's AUDIT.json."""
import sys
sys.dont_write_bytecode=True
import ast,json
from pathlib import Path
import mpmath as mp
mp.mp.dps=550
P=Path(__file__).resolve().parent
s=json.loads((P/'SUMMARY.json').read_text())
assert s['requested_samples']==32
assert s['all_requested_pairings_positive'] and s['all_requested_alternative_test_forms_negative']
assert s['full_sector_screens']==2560
assert s['minimum_stable_pairing_digits']>55
neg=s['negative_first_crossing'];assert mp.mpf(neg['pairing'])<0 and neg['stable_relative_digits']>235
assert mp.mpf(neg['alternative_carrier_test'])>0 and mp.mpf(neg['alternative_corrected_test'])>0
assert mp.mpf(neg['vacuum_leading_coefficient'])<0
actual=json.loads((P/'actual_sector_audit.json').read_text());assert len(actual)==17
assert all(c['schur_min_at_first_root']>0 for r in actual for c in r['checked'])
tiny=json.loads((P/'sectors_q2_R18_e1e-100_p120.json').read_text());assert tiny['complete'] and len(tiny['sectors'])==128
ini=json.loads((P/'initial_q2_R18_e1e-100_p160_s0_0.json').read_text())
assert all(ini['B_minus_D_inertia'][k]==v for k,v in ini['required_augmented_inertia'].items())
for p in P.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
assert not list(P.glob('*.lean'))
completed=['check','rank_check','path_identity','finish_primary','finish_screen_q1','final_screens',
 'initial_nonzero_inertia','finish_actual_low','finish_actual_high','leading_source','leading_vacuum',
 'tiny_actual_p400','ultratiny_first_q2_R18_e1e-100_p500','tiny_full_screen','tiny_initial',
 'actual_sector_audit_tiny','summary']
for name in completed:assert (P/(name+'.exit')).read_text().strip()=='0',name
missing=['batch_q2_R30_p180_a','finish_screen_q2']
for name in missing:assert not (P/(name+'.exit')).exists(),name
report=dict(status='passed-numerical-probe-audit; no formal closure',
 requested_grid_samples=32,requested_character_instances=2560,
 additional_negative_first_crossing=neg,
 additional_tiny_full_character_instances=128,
 python_files_parsed=len(list(P.glob('*.py'))),lean_files_authored=0,
 completed_driver_exits=completed,retained_timed_out_drivers_without_exit=missing,
 deliberately_unclaimed=['interval-certified signs','formal Fourier/operator dictionary',
   'full-character arbitrary-precision eigensolves','parametric q,R sign theorem',
   'GoalNeg2','any all-inverses-exist printed-form failure'],
 peak_RSS_KiB=s['max_peak_rss_KiB'])
(P/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print('AUDIT PASSED: 32 grid samples, actual sectors, stable NEGATIVE arbitrary-cap-regime example; no Lean closure.')
