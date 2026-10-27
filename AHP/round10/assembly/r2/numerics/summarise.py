#!/usr/bin/env python3
import json
from pathlib import Path
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.dps=280
a=json.loads((P/'left_q4_R20_p200.json').read_text())
b=json.loads((P/'left_q4_R20_p250.json').read_text())
def digits(x,y):
    x,y=mp.mpf(x),mp.mpf(y)
    return mp.nstr(-mp.log10(abs((x-y)/y)),16)
res=dict(status='evidence only; no exact dictionary, interval certificate, full-character screen, or cofinal proof',
    crossing=dict(q=4,R=20,character=[15,15],twist='left',precisions=[200,250],
      c1=b['c1'],K=b['K'],c1_agreement_digits=digits(a['c1'],b['c1']),
      v0=b['v0'],v0_agreement_digits=digits(a['v0'],b['v0']),
      residual_over_c1=b['residual_over_c1'],max_noninitial_jet_ratio=b['max_jet_ratio_away_from_0'],
      relative_pairing_error=b['source_pairing_relative_error'],source_blocks=b['nblocks'],
      peak_rss_KiB=max(a['peak_rss_KiB'],b['peak_rss_KiB'])),source_checks=[])
for prec in [150,190]:
    s=json.loads((P/f'source_q4_R20_p{prec}.json').read_text())
    res['source_checks'].append(dict(q=4,R=20,N=336,source_indices=[r['source_index'] for r in s['rows']],dps=prec,
        maximum_dictionary_error=mp.nstr(max(mp.mpf(r['max_dictionary_error']) for r in s['rows']),15),
        maximum_full_kkt_residual=mp.nstr(max(mp.mpf(r['full_kkt_residual']) for r in s['rows']),15),
        peak_rss_KiB=s['peak_rss_KiB']))
(P/'SUMMARY.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
