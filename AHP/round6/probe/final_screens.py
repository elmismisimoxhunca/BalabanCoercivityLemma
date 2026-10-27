#!/usr/bin/env python3
"""Independent p90 screen replaces no partial p70 artifacts.
The timed-out finish_screen q2 process is not relaunched.
"""
import sys
sys.dont_write_bytecode = True
from sectors import *
scan(2,30,'1e-5',90)
scan(2,30,'1e-6',70)  # not reached by the earlier timed-out batch
for eps in ['1e-5','1e-6']:
    initial(2,30,eps,70)
for R in [18,30]:
    for eps in ['1e-3','1e-6']:initial(2,R,eps,100)
