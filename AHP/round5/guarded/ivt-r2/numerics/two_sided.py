#!/usr/bin/env python3
"""Exploratory variant: two interior defects, never relabelled as dilU.
The second defect is at the last even x in Omega1. A bounded amplitude mask
satisfies the same frozen regularity bound, but no spectral theorem follows.
Uses local copies of the old transcriptions with a 1900 MiB address-space cap.
"""
import sys
sys.dont_write_bytecode=True
import json
from pathlib import Path
import crossing
import numpy as np

class TwoSided(crossing.SingleSlab):
    def config(self,theta,eps):
        u=super().config(theta,eps)
        u[((self.q-2,0,0),1)]=crossing.expv(np.array([eps,0.,0.]))
        return u

crossing.SingleSlab=TwoSided
if __name__=='__main__':
    R=int(sys.argv[1]) if len(sys.argv)>1 else 6
    eps=float(sys.argv[2]) if len(sys.argv)>2 else .0015625
    row=crossing.run(R,eps)
    row['variant']='Two defects at p and q-2; NOT the single-defect dilU.'
    (Path(__file__).parent/('two_sided_R%d_eps%g.json'%(R,eps))).write_text(json.dumps(row,indent=2)+'\n')
