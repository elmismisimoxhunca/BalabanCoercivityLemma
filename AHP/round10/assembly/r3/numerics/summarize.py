#!/usr/bin/env python3
"""Compare the independently executed 160/210-digit held-out runs; no new solves."""
from pathlib import Path
from decimal import Decimal, localcontext
import json
P=Path(__file__).resolve().parent
with localcontext() as ctx:
 ctx.prec=260
 a=json.loads((P/'energy_q2_R26_p160.json').read_text())
 b=json.loads((P/'energy_q2_R26_p210.json').read_text())
 out={'case':{'q':2,'R':26,'character':[7,7],'twist':'left-only'},'precision_digits':[160,210]}
 out['agreement']={}
 for key in ['root','canonical_c1','jet_scale','scaled_response_energy','adaptive_coupling_cell_normalized','max_scaled_curl']:
  x,y=Decimal(a[key]),Decimal(b[key]);rel=abs(x-y)/abs(y)
  out['agreement'][key]={'relative_error':str(rel),'relative_digits':str(-rel.log10())}
 for data in [a,b]:
  assert Decimal(data['scaled_response_energy'])>0
  assert Decimal(data['max_scaled_curl'])>0
  assert Decimal(data['canonical_c1'])<0
  assert Decimal(data['null_residual_over_c1'])<Decimal('1e-50')
  assert Decimal(data['curl_energy_error'])<Decimal('1e-150')
  assert Decimal(data['reciprocity_error'])<Decimal('1e-150')
  assert int(data['peak_rss_KiB'])<2*1024**2
 out['passes']=True
 out['normalization']='Cell-normalized floating-point evidence, not an identification with physical Lean aggregation.'
 out['not_proved']=['interval enclosure','all-character exclusion','whole-kernel definiteness','nested cofinality']
 (P/'SUMMARY.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
