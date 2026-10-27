#!/usr/bin/env python3
"""Per-character geometric collar model and dominant normalized constants.
The model is fitted on R=20,22,24 (or an explicitly supplied three-radius
sweep). All other radii are extrapolations until checked by independent data.
"""
from pathlib import Path
import argparse,json,mpmath as mp
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent

def old_area(q,R):
    if q==1:
        if R==20:p=ROOT/'AHP/round12/kernel/r1/star_right_q1_R20_p120.json'
        elif R in [22,24,26,28]:p=ROOT/f'AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json'
        elif R in [30,32]:p=ROOT/f'AHP/round14/assembly/r2/star_right_q1_R{R}_p120.json'
        else:return None
        d=json.loads(p.read_text());return 2*mp.mpf(d['first_physical_top_jet_sums'][1]),str(p)
    if q==2 and R==20:
        p=ROOT/'AHP/round12/kernel/r2/star_right_q2_R20_p155.json';d=json.loads(p.read_text())
        return 2*mp.mpf(d['first_physical_top_jet_sums'][1]),str(p)
    if q==4 and R==18:
        p=ROOT/'AHP/round14/pathchoice/r2/long_q4_R18_L3_L3_q4_R18.json';d=json.loads(p.read_text())
        for v in d['variants']:
            if v['name']=='original':return 2*mp.mpf(v['first_physical_top_jet_sums'][1][0]),str(p)
    return None

def run(sweep,dps):
    mp.mp.dps=dps;D=json.loads(Path(sweep).read_text());q=D['q'];N=4*q;records=D['records']
    assert sorted(set(r['R'] for r in records))==[20,22,24]
    chars=sorted(set(tuple(r['character']) for r in records));models=[]
    for c in chars:
        rr=sorted([r for r in records if tuple(r['character'])==c],key=lambda r:r['R'])
        a20,a22,a24=[mp.mpf(r['sector_areaSum']) for r in rr]
        ratio=a24/a22
        models.append({'character':list(c),'raw_area_R22':a22,'ratio_per_two_radius':ratio,
          'ratio_R20_to_R22_check':a22/a20,'ratio_R22_to_R24_check':a24/a22,
          'geometric_model':f'raw_c(R) = raw_c(22) * ratio^((R-22)/2)'})
    radii=list(range(18,42,2));dominant=max(m['ratio_per_two_radius'] for m in models)
    table=[];checks=[]
    for R in radii:
        raw=sum(m['raw_area_R22']*m['ratio_per_two_radius']**(mp.mpf(R-22)/2) for m in models)
        area=raw/(N*N);K=area/(dominant**(mp.mpf(R)/2))
        row={'R':R,'areaSum_model':area,'dominant_ratio_per_two_radius':dominant,
          'normalized_leading_constant_model':K}
        old=old_area(q,R)
        if old is not None:
            value,path=old;row.update({'areaSum_independent':value,'independent_path':path,
              'model_minus_independent_over_independent':area/value-1,
              'normalized_leading_constant_independent':value/dominant**mp.mpf(R)/2})
            checks.append(row)
        table.append(row)
    result={'q':q,'dps':dps,'source_sweep':sweep,'drive':D['drive'],'root':D['root'],
      'per_character_models':models,'dominant_ratio_per_two_radius':dominant,
      'normalization':'K_R = areaSum_R / dominant_ratio^(R/2); ratio is per R -> R+2',
      'table':table,'independent_checks':checks,
      'max_abs_model_relative_error_on_independent_checks':max((abs(r['model_minus_independent_over_independent']) for r in checks),default=mp.mpf(0)),
      'qualification':'Non-interval numerical evidence. Per-character ratios are fitted on R=20,22,24. Other radii are model extrapolations unless an independent path is shown. Not a Lean or cofinal proof.'}
    target=OUT/f'area_model_right_q{q}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('OUTPUT',target,'dominant',dominant,'max check error',result['max_abs_model_relative_error_on_independent_checks'])
    for r in table:print(R if False else r['R'],mp.nstr(r['areaSum_model'],16),mp.nstr(r['normalized_leading_constant_model'],22),mp.nstr(r.get('model_minus_independent_over_independent',mp.mpf(0)),5))
def jsonable(x):
    if isinstance(x,(mp.mpf,mp.mpc)):return mp.nstr(x,mp.mp.dps-5)
    if isinstance(x,dict):return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [jsonable(v) for v in x]
    return x
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--sweep',required=True);ap.add_argument('--dps',type=int,default=70)
    a=ap.parse_args();run(a.sweep,a.dps)
