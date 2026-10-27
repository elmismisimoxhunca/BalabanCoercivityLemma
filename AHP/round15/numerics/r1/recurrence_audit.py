#!/usr/bin/env python3
"""Fit and independently check per-character flat-collar recurrences.
The fit window excludes six layers at both interfaces; those interface rows are
then evaluated separately rather than silently included in the bulk model.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import argparse,json,glob,mpmath as mp
OUT=Path(__file__).resolve().parent

def cv(s):
    p=s.strip().strip('()').split()
    if len(p)==2:return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1][:-1]))
    return mp.mpc(mp.mpf(p[0]),mp.mpf(p[1]+p[2][:-1]))

def fit(r,order,start,stop):
    M=mp.matrix(order);rhs=mp.matrix(order,1)
    for base in range(start,stop-order):
        vals=[cv(r[base+j]['w']) for j in range(order+1)];scale=max(map(abs,vals))
        if not scale:continue
        wt=1/scale;row=[v*wt for v in vals[:-1]];target=vals[-1]*wt
        for a in range(order):
            rhs[a]+=mp.re(mp.conj(row[a])*target)
            for b in range(order):M[a,b]+=mp.re(row[a]*mp.conj(row[b]))
    try:sol=M**-1*rhs
    except Exception:return None,None
    return [sol[j] for j in range(order)],(start,stop)

def residual(r,co,start,stop):
    order=len(co);ans=mp.mpf(0);worst=None
    for base in range(start,stop-order):
        vals=[cv(r[base+j]['w']) for j in range(order+1)];scale=max(map(abs,vals))
        if not scale:continue
        res=vals[-1]-sum(co[j]*vals[j] for j in range(order));rel=abs(res)/scale
        if rel>ans:ans=rel;worst=r[base+order]['x']
    return ans,worst

def components(D):
    ans={}
    for r in D['records']:
        x,d=r['bond'];key=(d,tuple(x[1:]))
        ans.setdefault(key,[]).append(r)
    for v in ans.values():v.sort(key=lambda r:r['x'])
    return ans

def run(pattern,dps):
    mp.mp.dps=dps;results=[]
    for fn in sorted(glob.glob(pattern)):
        D=json.loads(Path(fn).read_text());comps=components(D);probe=comps[(0,(0,0))]
        start=6;stop=len(probe)-6;chosen=None;errors={}
        for order in [2,4,6,8,10,12]:
            co,window=fit(probe,order,start,stop)
            if co is None:continue
            err,worst=residual(probe,co,start,stop);errors[str(order)]={'relative_residual':err,'at':worst}
            if err<mp.mpf('1e-9'):
                chosen=co;break
        if chosen is None:
            results.append({'file':fn,'q':D['q'],'R':D['R'],'character':D['character'],'status':'no bulk fit <=12','errors':errors});continue
        order=len(chosen);allres={};interfaces={}
        for key,seq in comps.items():
            tag=f'{key[0]}:{key[1][0]}:{key[1][1]}'
            allres[tag]=residual(seq,chosen,start,stop)[0]
            interfaces[tag]={
              'inner':residual(seq,chosen,0,min(12,len(seq)-order))[0],
              'outer':residual(seq,chosen,max(0,len(seq)-12),len(seq)-order)[0]}
        poly=[1]+[-chosen[j] for j in range(order-1,-1,-1)]
        try:roots=mp.polyroots(poly,maxsteps=200)
        except Exception:roots=[]
        results.append({'file':fn,'q':D['q'],'R':D['R'],'character':D['character'],'status':'fitted',
          'order':order,'coefficients':chosen,'bulk_probe_relative_residual':residual(probe,chosen,start,stop)[0],
          'all_component_bulk_relative_residual_max':max(allres.values()),
          'component_bulk_residuals':allres,'interface_relative_residuals':interfaces,
          'roots':roots,'fit_errors':errors,
          'convention':'w[n+m] = sum coefficients[j] * w[n+j], m=order; residual relative to largest adjacent magnitude'})
    result={'dps':dps,'results':results,'qualification':'Non-interval recurrence fit; interface rows are reported separately, not asserted to satisfy the bulk polynomial.'}
    target=OUT/'recurrence_audit.json';target.write_text(json.dumps(jsonable(result),indent=2)+'\n');print('OUTPUT',target)
    for r in results:print(r['q'],r['character'],r['status'],'order',r.get('order'),'bulk',r.get('all_component_bulk_relative_residual_max'),'roots',r.get('roots'))
def jsonable(x):
    if isinstance(x,(mp.mpf,mp.mpc)):return mp.nstr(x,mp.mp.dps-5)
    if isinstance(x,dict):return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [jsonable(v) for v in x]
    return x
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--pattern',required=True);ap.add_argument('--dps',type=int,default=60)
    a=ap.parse_args();run(a.pattern,a.dps)
