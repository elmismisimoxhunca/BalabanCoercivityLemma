#!/usr/bin/env python3
"""Full-character numerical screens and high-precision zero-sector inertias.
Run through heavy run. Existing completed artifacts are retained, not rerun.
"""
import sys
sys.dont_write_bytecode = True
from sectors import *
q=int(sys.argv[1])
for R in [18,20,24,30]:
    for eps in ['1e-3','1e-4','1e-5','1e-6']:
        p=OUT/f'sectors_q{q}_R{R}_e{eps}.json'
        if not p.exists() or not json.loads(p.read_text()).get('complete'):scan(q,R,eps)
        p=OUT/f'initial_q{q}_R{R}_e{eps}_p70_s0_0.json'
        if not p.exists():initial(q,R,eps,70)
# Independent mp inertias at both geometrical extremes and amplitude endpoints.
for R in [18,30]:
    for eps in ['1e-3','1e-6']:
        p=OUT/f'initial_q{q}_R{R}_e{eps}_p100_s0_0.json'
        if not p.exists():initial(q,R,eps,100)
