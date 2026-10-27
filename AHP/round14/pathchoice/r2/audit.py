#!/usr/bin/env python3
"""Audit round-14 path-choice R2 artifacts and evidence boundaries."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'AHP/round14/pathchoice/r2'
SHARED=ROOT/'AHP/round14/shared/pathchoice'
permitted={'propext','Classical.choice','Quot.sound'}
external_new={
 'AdalyFormal.Round4.Guarded.RefuteR1.dil_shift_zero',
 'AdalyFormal.Round5.Guarded.IVTR2.rightSite_bd',
 'AdalyFormal.Round9.Guarded.QualitativeR2.AnM',
 'AdalyFormal.Round9.Guarded.QualitativeR2.AnFam',
 'AdalyFormal.Round9.Guarded.QualitativeR2.analyticAt_exp_I',
 'AdalyFormal.Round9.Guarded.QualitativeR2.anM_uMat',
 'AdalyFormal.Round12.Kernel.Actual.chargedCoordinate',
}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def records(p):
    text=p.read_text()
    return [(n,d) for n,d in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)]

lean=[]
for local_name,shared_name,expected_pc,expected_ext in [
    ('LongArm.lean','R2_LongArm.lean',52,7),
    ('LongCrossing.lean','R2_LongCrossing.lean',18,0)]:
    local=OUT/local_name; shared=SHARED/shared_name
    assert local.read_bytes()==shared.read_bytes()
    entry={'local':str(local.relative_to(ROOT)),'shared':str(shared.relative_to(ROOT)),
           'sha256':sha(local),'byte_identical':True,'lines':len(local.read_text().splitlines())}
    for p in [local,shared]:
        assert Path(str(p)+'.exit').read_text().strip()=='0'
        log=Path(str(p)+'.log').read_text()
        assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
        rec=records(Path(str(p)+'.log'))
        assert all({x.strip() for x in d.split(',')}<=permitted for n,d in rec)
        pc=[n for n,d in rec if n.startswith('AdalyFormal.Round14.PathChoice.')]
        ext=[n for n,d in rec if n in external_new]
        assert len(pc)==expected_pc,(p,len(pc),expected_pc)
        assert len(ext)==expected_ext,(p,len(ext),expected_ext)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',p.read_text())
        entry.setdefault('executions',[]).append({'path':str(p.relative_to(ROOT)),'exit':0,
            'axiom_records':len(rec),'new_pathchoice_records':len(pc),
            'other_new_records':len(ext),'warnings':0,'errors':0,'sorryAx':0,
            'forbidden_mechanisms':False})
    lean.append(entry)

q4=json.loads((OUT/'tail_q4_R18_c2_m0_25_c3_m2_25_p110.json').read_text())
r=q4['right_row']
assert q4['dps']==110 and q4['right_row_j']==303
assert r['negative_count']==0 and r['positive_count']==256 and r['common_weak_sign']
assert r['sum']!='0' and float(r['max_over_abs_sum'])<0.007
assert float(r['abs_sum_over_l1'])==1.0
assert float(q4['flat_resolvent_absolute_residual'])<1e-100
q2=json.loads((OUT/'tail_q2_R20_c2_m0_25_c3_m2_25_p110.json').read_text())
r2=q2['right_row']
assert q2['dps']==110 and r2['negative_count']==2 and r2['positive_count']==62
assert float(r2['max_over_abs_sum'])<0.042 and float(r2['abs_sum_over_l1'])>0.9995
assert float(q2['flat_resolvent_absolute_residual'])<1e-100
q22=json.loads((OUT/'long_q2_R22_L3_L3_q2_R22.json').read_text())
v22=next(v for v in q22['variants'] if v['name']=='candidate')
assert v22['status']=='candidate' and v22['max_over_abs_sum'][1]<0.056
assert min(v22['central_zero_schur_min_at_0_root_halfpi'][1:])>0
q420=json.loads((OUT/'long_q4_R20_L3_L3_q4_R20.json').read_text())
v420=next(v for v in q420['variants'] if v['name']=='candidate')
assert v420['status']=='candidate'
assert all(z[0]>0 for z in v420['first_top_jet_cells'][1])
assert v420['max_over_abs_sum'][1]<0.006
q1=json.loads((OUT/'long_q1_R20_L3_L3_q1_R20.json').read_text())
v1=next(v for v in q1['variants'] if v['name']=='candidate')
assert v1['max_over_abs_sum'][1]>30
cluster=json.loads((OUT/'cluster_q2_R20_2x0.json').read_text())
orig=next(v for v in cluster['variants'] if v['name']=='original_only')
equal=next(v for v in cluster['variants'] if v['name']=='equal')
assert orig['status']=='candidate' and abs(orig['root']-1.2080305375347544)<1e-10
assert equal['max_over_abs_sum'][1]>1.7 and equal['max_over_abs_sum'][2]>2.3
sweep=json.loads((OUT/'long_q4_R18_L3_L3_q4_sweep.json').read_text())
common=[]
for v in sweep['variants']:
    cells=v['first_top_jet_cells'][1]; total=v['first_physical_top_jet_sums'][1][0]
    if (all(z[0]>=0 for z in cells) and total>0) or (all(z[0]<=0 for z in cells) and total<0):
        common.append(v['name'])
assert common==['c2_-0.25_c3_-2.25']
exit_names=[
 'screen_cluster_2x0.exit','screen_longer_L3.exit','screen_tail_sweep_L3.exit',
 'screen_tail_targeted_L3.exit','screen_tail_q1_R20.exit','screen_tail_q2_R22.exit',
 'screen_tail_q4_R18.exit','screen_tail_q4_R20.exit','screen_tail_q4_sweep.exit',
 'verify_tail_q2_R20_p110.exit','verify_tail_q4_R18_p110.exit']
for name in exit_names: assert (OUT/name).read_text().strip()=='0',name
summary={
 'verdict':'A genuinely better modified path is found numerically. Its negative-pi endpoint is proved; original P3 and the remaining crossing-positivity and area inputs stay open. Lean proves path infrastructure and conditional reductions only.',
 'lean':lean,
 'tail_endpoint':{'proved':True,'theorem':'AdalyFormal.Round14.PathChoice.tailEndpointNegative',
   'crossing_theorem':'AdalyFormal.Round14.PathChoice.tailKernelLinePackage_of_crossingPositive',
   'scope':'Unconditional negative-pi input; whole kernel line remains conditional on TailCrossingPositive.'},
 'q4_R18_high_precision':{
   'dps':110,'right_row_j':q4['right_row_j'],'root_double':q4['root_double'],
   'positive_cells':r['positive_count'],'negative_cells':r['negative_count'],
   'sum':r['sum'],'max_over_abs_sum':r['max_over_abs_sum'],'abs_sum_over_l1':r['abs_sum_over_l1'],
   'residual':q4['flat_resolvent_absolute_residual'],
   'scope':'High-precision dressed solve from a double-precision drive; not a root enclosure or proof.'},
 'q4_R20_double':{'root':v420['root'],'positive_cells':sum(z[0]>0 for z in v420['first_top_jet_cells'][1]),
   'negative_cells':sum(z[0]<0 for z in v420['first_top_jet_cells'][1]),
   'ratio':v420['max_over_abs_sum'][1],'scope':'Double-precision non-interval evidence only.'},
 'q2_R20_high_precision':{'dps':110,'right_row_j':q2['right_row_j'],
   'positive_cells':r2['positive_count'],'negative_cells':r2['negative_count'],
   'ratio':r2['max_over_abs_sum'],'abs_sum_over_l1':r2['abs_sum_over_l1'],
   'residual':q2['flat_resolvent_absolute_residual']},
 'q2_R22_double':{'root':v22['root'],'ratio':v22['max_over_abs_sum'][1],
   'central_zero_minima':v22['central_zero_schur_min_at_0_root_halfpi']},
 'q1_caution':{'ratio':v1['max_over_abs_sum'][1],
   'scope':'The same coefficients do not give a uniform all-q common-sign regime; q=1 is outside the dyadic cofinal sequence after j=0.'},
 'q4_sweep':{'variants':len(sweep['variants']),
   'common_sign_variants':common},
 'cluster_control':{'original_root':orig['root'],'equal_ratios':equal['max_over_abs_sum'],
   'scope':'Same-side double stars did not improve cancellation.'},
 'screen_exits':{name:0 for name in exit_names},
 'qualification':'All numerical values are non-interval evidence only. No numerical root, sign, nonzero sum, P1/P2/KernelLine, or cofinal statement is used as a Lean premise.'
}
(OUT/'AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
