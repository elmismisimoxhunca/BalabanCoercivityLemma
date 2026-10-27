#!/usr/bin/env python3
"""Finite-difference smallness/one-spike diagnostic, not a cap/cofinal proof.

All modeled operators and anchors are those of wide_probe.py and assembly.py.
The single-defect variant sets the second defect to identity; the remaining
link is exp(epsilon*diag(i,-i)) at ((2R+4,0,0),1), repeated with period two.
This is not claimed to be the frozen nonvacuity spike (different location and
transverse periodic repetition), or to satisfy ClassCoupled.
"""
import sys
sys.dont_write_bytecode = True
import gc,json
import wide_probe as wp
from assembly import I

Base=wp.WideSlab
class OneSpike(Base):
    def config(self,theta,eps):
        u=super().config(theta,eps)
        u[((self.p+1,1,0),2)]=I.copy()
        return u

if __name__=='__main__':
    result=dict(status='diagnostic only; no exact eigenvalue or in-class certificate',results=[])
    for mode in ('two_spikes','one_spike'):
        wp.WideSlab=Base if mode=='two_spikes' else OneSpike
        for eps in (.04,.02,.01):
            row=wp.run(2,eps);row['mode']=mode;result['results'].append(row)
            gc.collect()
            (wp.OUT/'smallness_results.json').write_text(json.dumps(result,indent=2))
