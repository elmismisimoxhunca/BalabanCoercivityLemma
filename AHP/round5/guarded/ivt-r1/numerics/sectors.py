#!/usr/bin/env python3
"""All carrier Fourier sectors at the R=2 diagnostic pre-crossing point.
Each sector is assembled before inverses; Q uses Taylor jets. This is floating
point, not a certified lower bound or a Lean Fourier dictionary.
"""
import sys
sys.dont_write_bytecode=True
import gc,itertools,json,time,resource
from pathlib import Path
from crossing import SingleSlab
from lift_probe import sector,local_raw
OUT=Path(__file__).resolve().parent
R=2;eps=.0015625
c=json.loads((OUT/'crossing_R2_eps0.0015625.json').read_text())
theta=c['near_crossing'][-1]['theta']
lat=SingleSlab(R);u=lat.config(0,eps);rows=[local_raw(lat,u,b) for b in lat.b1]
payload=dict(R=R,epsilon=eps,theta=theta,physical_sides=[40,8,8],sectors=[],
 warning='Floating-point sector transcriptions only. No exact positivity or intertwining theorem.')
start=time.time()
for iy,iz in itertools.product(range(4),repeat=2):
    row=sector(R,eps,theta,iy,iz,rows)
    payload['sectors'].append(row);print(json.dumps(row),flush=True);gc.collect()
payload['seconds']=time.time()-start
payload['minimum_carrier_eigenvalue']=min(s['lowest_six'][0] for s in payload['sectors'])
payload['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
(OUT/'sectors_R2.json').write_text(json.dumps(payload,indent=2)+'\n')
