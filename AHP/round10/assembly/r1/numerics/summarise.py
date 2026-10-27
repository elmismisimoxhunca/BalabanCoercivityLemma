#!/usr/bin/env python3
"""Compare independently recomputed precision runs; never a proof certificate."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 240
HERE = Path(__file__).resolve().parent
rows = {p: json.loads((HERE/f'left_q2_R22_p{p}.json').read_text()) for p in (140,190,220)}
agreement = {}
for a,b in ((140,190),(190,220)):
    for key in ('c1','K','root','exact_pencil_slope'):
        x,y = mp.mpf(rows[a][key]), mp.mpf(rows[b][key])
        err = abs((x-y)/y)
        agreement[f'{a}_vs_{b}_{key}_relative_digits'] = mp.nstr(-mp.log10(err), 12)
out = dict(agreement=agreement,
    q=2,R=22,character=[7,7],twist='left-only',
    runs=[{k:row[k] for k in ('dps','c1','K','null_residual','residual_over_c1','peak_rss_KiB','seconds')}
          for row in rows.values()],
    source_domination_check={key:rows[220][key] for key in
        ('nblocks','v0','max_jet_ratio','max_jet_ratio_away_from_0',
         'source_pairing_relative_error','source_pairing_error_bound','source_equation_residual')},
    proof_certificate=False,
    caveat='Shared round6 transcription; independently rerun at a held-out radius. Not an independent operator transcription, interval enclosure, or full-character screen.')
(HERE/'SUMMARY.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
