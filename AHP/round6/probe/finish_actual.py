#!/usr/bin/env python3
"""Actual q=2 first character (7,7), not the provisional zero character."""
import sys
sys.dont_write_bytecode = True
from probe import *
mode=sys.argv[1]
precisions={'low':[(18,300),(20,340),(24,420),(30,520)],
            'high':[(18,400),(20,440),(24,520),(30,640)]}[mode]
for R,dps in precisions:
 for eps in ['1e-3','1e-4','1e-5','1e-6']:
  path=OUT/f'q2_R{R}_e{eps}_p{dps}_s7_7.json'
  if not path.exists():run(2,R,eps,dps,7,7)
