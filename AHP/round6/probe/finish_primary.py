#!/usr/bin/env python3
"""Remaining independent precision checks; do not retry the interrupted job."""
import sys
sys.dont_write_bytecode = True
from probe import *
for R,dps in [(18,200),(20,200),(24,210),(30,220)]:
    for eps in ['1e-3','1e-4','1e-5','1e-6']:
        path=OUT/f'q2_R{R}_e{eps}_p{dps}_s0_0.json'
        if not path.exists():run(2,R,eps,dps)
# New precision, not a relaunch of the interrupted p180 e1e-6 calculation.
for eps in ['1e-4','1e-5','1e-6']:
    path=OUT/f'q2_R30_e{eps}_p190_s0_0.json'
    if not path.exists():run(2,30,eps,190)
# Stability checks through the left/right mixing transition.
for eps in ['1e-18','1e-25','1e-40']:
    path=OUT/f'q1_R18_e{eps}_p200_s0_0.json'
    if not path.exists():run(1,18,eps,200)
