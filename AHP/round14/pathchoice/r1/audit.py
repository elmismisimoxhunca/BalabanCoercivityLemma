#!/usr/bin/env python3
"""Validate round-14 path-choice controls and summarize non-interval evidence."""
from pathlib import Path
import hashlib,json,math,re
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'AHP/round14/pathchoice/r1'
load=lambda name:json.loads((OUT/name).read_text())
base=load('shifts_q2_R20.json')['placements'][0]
assert base['shift']==[0,0]
old=json.loads((ROOT/'AHP/round12/kernel/r2/star_right_q2_R20_p155.json').read_text())
old_ratios=[float(m)/abs(float(s)) for m,s in zip(old['max_abs_first_top_jet'],old['first_physical_top_jet_sums'])]
def close(a,b,tol=1e-9):return abs(a-b)<=tol*max(1,abs(a),abs(b))
control={'root_relative_error':abs(base['root']-float(old['root']))/abs(float(old['root'])),
         'ratios':base['max_over_abs_sum'],'retained_ratios':old_ratios}
assert control['root_relative_error']<1e-12
assert all(close(a,b,1e-9) for a,b in zip(base['max_over_abs_sum'],old_ratios))
for a,b in zip(base['first_physical_top_jet_sums'],old['first_physical_top_jet_sums']):
    assert close(a[0],float(b),1e-9)
# Even fine translations must preserve every aggregate and its maximum.
even_errors=[]
for p in load('shifts_q2_R20.json')['placements']:
    if p['shift'][0]%2==0 and p['shift'][1]%2==0:
        even_errors.append(max(abs(a-b) for a,b in zip(p['max_over_abs_sum'],base['max_over_abs_sum'])))
        for key in ['first_physical_top_jet_sums','max_abs_first_top_jet']:
            for x,y in zip(p[key],base[key]):
                xv=x[0] if isinstance(x,list) else x;yv=y[0] if isinstance(y,list) else y
                even_errors.append(abs(xv-yv)/max(1e-300,abs(yv)))
assert max(even_errors)<1e-12
odd=[p for p in load('shifts_q2_R20.json')['placements'] if p['shift'][0]%2 or p['shift'][1]%2]
odd_best=min((r,p['shift'],i) for p in odd for i,r in enumerate(p['max_over_abs_sum']))
# Other family controls use the same original root and cell ratios.
long_ext=load('long_q2_R20_L2_extensions.json')
long_orig=next(v for v in long_ext['variants'] if v['name']=='original')
assert close(long_orig['root'],base['root'],1e-12)
assert all(close(a,b,1e-9) for a,b in zip(long_orig['max_over_abs_sum'],base['max_over_abs_sum']))
signed=load('signed_q2_R20_all.json')
signed_orig=next(v for v in signed['variants'] if v['signs']==[1,1,1,1])
assert close(signed_orig['root'],base['root'],1e-12)
assert all(close(a,b,1e-9) for a,b in zip(signed_orig['max_over_abs_sum'],base['max_over_abs_sum']))
double=load('double_q2_R20.json')
double_orig=next(v for v in double['variants'] if v['cL']==0 and v['cR']==1)
assert close(double_orig['root'],base['root'],1e-12)
assert all(close(a,b,1e-9) for a,b in zip(double_orig['max_over_abs_sum'],base['max_over_abs_sum']))
double_equal=next(v for v in double['variants'] if v['cL']==1 and v['cR']==1)
assert double_equal['status']=='rejected' and abs(double_equal['charged_low'][1])<1e-6
# Candidate is only a numerical screening label, never a theorem.
arm=load('signed_q2_R20_coefficients.json')['variants']
armc=[v for v in arm if v['status']=='candidate']
arm_best=min((max(v['max_over_abs_sum'][1:]),v) for v in armc)
long=load('long_q2_R20_L2_second_coeffs.json')['variants']
longc=[v for v in long if v['status']=='candidate']
long_best=min((max(v['max_over_abs_sum'][1:]),v) for v in longc)
assert long_best[1]['name']=='all_-1.0'
replay=load('long_alternating_q2_R20_p110.json')
assert replay['dps']==110
assert max(replay['comparison_with_double_cached_columns']['ratio_absolute_differences'])<1e-8
assert max(replay['comparison_with_double_cached_columns']['sum_relative_differences'])<1e-8
assert float(replay['flat_resolvent_absolute_residual'])<1e-100
# Compilation and publication checks.
local=OUT/'PathChoice.lean';shared=ROOT/'AHP/round14/shared/pathchoice/R1_WeightedStar.lean'
assert local.read_bytes()==shared.read_bytes()
for p in [local,shared]:
    assert (Path(str(p)+'.exit')).read_text().strip()=='0'
    log=Path(str(p)+'.log').read_text()
    assert 'error:' not in log and 'warning:' not in log
    records=[(name,deps) for name,deps in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log,re.S)
             if name.startswith('AdalyFormal.Round14.PathChoice.')]
    assert len(records)==16,(p,len(records))
    permitted={'propext','Classical.choice','Quot.sound'}
    assert all({d.strip() for d in deps.split(',')}<=permitted for _,deps in records)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',p.read_text())
for p in list(OUT.glob('screen_*.exit'))+[OUT/'verify_long_mp.exit']:
    assert p.read_text().strip()=='0',p
summary={
 'qualification':'All numerical results are double-precision non-interval evidence only. Candidate labels are screening diagnostics, not proved P1/P2/KernelLine facts. No nonzero jet is a Lean certificate.',
 'original_control':control,
 'even_shift_max_relative_error':max(even_errors),
 'odd_shift_best':{'ratio':odd_best[0],'shift':odd_best[1],'direction':odd_best[2]},
 'arm_coefficients':{'variant_count':len(arm),'candidate_count':len(armc),
   'best_worst_tangential_ratio':arm_best[0],'coefficients':arm_best[1]['signs'],'root':arm_best[1]['root']},
 'length_two_alternating':{'variant_count':len(long),'candidate_count':len(longc),
   'best_worst_tangential_ratio':long_best[0],'name':long_best[1]['name'],'root':long_best[1]['root'],
   'ratios':long_best[1]['max_over_abs_sum'],
   'central_zero_diagnostic_min':min(long_best[1]['central_zero_schur_min_at_0_root_halfpi'])},
 'double_star_equal_strength':{'status':double_equal['status'],'second_eigenvalue':double_equal['charged_low'][1]},
 'alternating_high_precision_replay':{'dps':replay['dps'],
   'ratios':[float(x) for x in replay['max_over_abs_sum']],
   'flat_residual':replay['flat_resolvent_absolute_residual'],
   'comparison':replay['comparison_with_double_cached_columns'],
   'scope':'High-precision response from a double-precision drive; not a high-precision root or proof.'},
 'lean':{'local':'AHP/round14/pathchoice/r1/PathChoice.lean',
   'shared':'AHP/round14/shared/pathchoice/R1_WeightedStar.lean','new_axiom_records_each':16,
   'source_sha256':hashlib.sha256(local.read_bytes()).hexdigest(),'exit_each':0,
   'byte_identical':True,'forbidden_mechanisms':False},
 'verdict':'No screened modified family reaches a dominant-cell or common-sign regime. P3, CofinalP3 and GoalNeg2 remain open.'
}
(OUT/'AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
