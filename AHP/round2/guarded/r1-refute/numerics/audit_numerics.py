#!/usr/bin/env python3
"""Additional checks for the small numerical assembly, not Lean verification.
All modeled operators and frozen source anchors: probe_assembled.py header.
The flat Q check expands the first derivative of R2Raw1.rawStep (line 74):
staircase contributions cancel, leaving the average of the straight paths.
"""
import sys
sys.dont_write_bytecode=True
import json
import numpy as np
from probe_assembled import Slab,Raw,OUT,assemble
lat=Slab();flat=Raw(lat,lat.config(0.,0.));q=flat.jac(2e-5)
exact=np.zeros_like(q);emap={i:j for j,i in enumerate(lat.eidx)}
for r,(x,mu) in enumerate(lat.b1):
    for o in lat.offs:
        y=tuple(x[i]+o[i] for i in range(3))
        for j in lat.path(y,[mu,mu]):
            for c in range(3):exact[3*r+c,emap[3*j+c]]+=1/16
flat_error=float(np.max(np.abs(q-exact)))
assert flat_error<1e-9
raw,W,_,_,checks=assemble(lat,0.16)
rng=np.random.default_rng(991);xs=rng.normal(size=(3,lat.dim))*0.01
moved=Raw(lat,lat.config(0.7,0.16))
raw_const=float(np.max(np.abs(raw.eval(xs)-moved.eval(xs))))
j_const=float(np.max(np.abs(lat.jsource(lat.config(0.7,0.16))-lat.jsource(lat.config(0.,0.16)))))
outside=np.setdiff1d(np.arange(lat.dim),lat.eidx)
w_outside=float(np.max(np.abs(W[outside])))
assert raw_const<1e-12 and j_const<1e-12 and w_outside<1e-12
out=dict(flat_Q_error=flat_error,raw_theta_const_error=raw_const,J_theta_const_error=j_const,
    W_outside_E_error=w_outside,source_checks=checks,
    fine_sides=lat.sides,unit_sides=[n//2 for n in lat.sides],
    TorusOK_strict_ell_below_each_unit_side=all(2<n//2 for n in lat.sides),
    note='numerical checks only; TorusOK fails and no cofinal class is supplied')
print(json.dumps(out,indent=2))
(OUT/'audit_results.json').write_text(json.dumps(out,indent=2))
