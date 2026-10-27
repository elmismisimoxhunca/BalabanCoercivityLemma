#!/usr/bin/env python3
"""Cross-precision evidence, not a proof or interval enclosure."""
from pathlib import Path
import hashlib, json
import mpmath as mp
mp.mp.dps=270
P=Path(__file__).resolve().parent
runs={}
for dps in (180,230,240):
 p=P/f'energy_q2_R28_p{dps}.json'
 assert p.with_suffix('.exit').read_text().strip()=='0'
 assert 'RESULT' in p.with_suffix('.log').read_text()
 d=json.loads(p.read_text())
 assert d['q']==2 and d['R']==28 and d['character']==[7,7] and d['twist']=='left-only'
 assert d['peak_rss_KiB']<2*1024**2
 assert mp.mpf(d['canonical_c1'])<0
 assert mp.mpf(d['scaled_response_energy'])>0
 runs[dps]=d
keys=['root','canonical_c1','jet_scale','scaled_response_energy','adaptive_coupling_cell_normalized']
comparisons=[]
for a,b in ((180,230),(230,240)):
 digits={}
 for k in keys:
  x,y=mp.mpf(runs[a][k]),mp.mpf(runs[b][k])
  err=abs((x-y)/y)
  digits[k]=str(-mp.log10(err)) if err else 'exact serialized match'
 comparisons.append({'precisions':[a,b],'relative_digits':digits})
result={'case':{'q':2,'R':28,'twist':'left-only','character':[7,7]},
 'precisions':list(runs),'comparisons':comparisons,
 'highest_precision_result':runs[240],
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(P.glob('energy_q2_R28_p*.*'))},
 'qualification':'Numerical evidence only: no interval enclosure, no full-character spectral exclusion, no full-kernel/common-profile definiteness, no cofinal proof, no physical Lean aggregate normalization identification. The adaptive coupling is cell-normalized.'}
(P/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
for x in comparisons:
 print(x['precisions'],{k:float(v) for k,v in x['relative_digits'].items()})
print('240-digit residuals:',{k:runs[240][k] for k in ['null_residual_over_c1','curl_energy_error','reciprocity_error','full_lift_kkt_residual','full_source_kkt_residual','peak_rss_KiB']})
