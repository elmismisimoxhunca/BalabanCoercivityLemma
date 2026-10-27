#!/usr/bin/env python3
"""Exact algebraic rate candidates matched to the per-character area sweep."""
from pathlib import Path
import argparse,json,mpmath as mp
OUT=Path(__file__).resolve().parent

def run(model_path,dps):
    mp.mp.dps=dps;D=json.loads(Path(model_path).read_text());q=D['q'];N=4*q
    rows=[]
    for m in D['per_character_models']:
        iy,iz=m['character'];cy=mp.cos(mp.pi*iy/N);cz=mp.cos(mp.pi*iz/N)
        if iy==iz==0:
            s=mp.mpf(7);reason='charged-area suppresses the uniform s=3 channel; next channel s=7'
        else:
            s=7-2*(abs(cy)+abs(cz));reason='s = 7 - 2*(|cos(pi*iy/(4q))| + |cos(pi*iz/(4q))|)'
        rho=(s-mp.sqrt(s*s-4))/2;expected=rho**(8*q);actual=mp.mpf(m['ratio_per_two_radius'])
        rows.append({'character':[iy,iz],'s':s,'rho_small':rho,'rho_large':1/rho,
          'expected_area_ratio_per_two_radius':expected,'measured_area_ratio_per_two_radius':actual,
          'relative_error':actual/expected-1,'reason':reason,
          'quadratic_recurrence':'x_(n+2) = s*x_(n+1) - x_n; small root rho solves rho^2-s*rho+1=0',
          'area_exponent':'raw area ratio per R->R+2 is rho^(8q)'})
    result={'q':q,'dps':dps,'rows':rows,
      'max_abs_relative_error':max(abs(r['relative_error']) for r in rows),
      'qualification':'Exact algebraic candidate rates matched against non-interval R=20,22,24 data. This is not a proof of the recurrence or of cofinality.'}
    target=OUT/f'rate_table_right_q{q}.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n')
    print('OUTPUT',target,'max error',result['max_abs_relative_error'])
    for r in rows:print(r['character'],'s',mp.nstr(r['s'],20),'rho',mp.nstr(r['rho_small'],20),'rel',mp.nstr(r['relative_error'],5))
def jsonable(x):
    if isinstance(x,(mp.mpf,mp.mpc)):return mp.nstr(x,mp.mp.dps-5)
    if isinstance(x,dict):return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [jsonable(v) for v in x]
    return x
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--model',required=True);ap.add_argument('--dps',type=int,default=70)
    a=ap.parse_args();run(a.model,a.dps)
