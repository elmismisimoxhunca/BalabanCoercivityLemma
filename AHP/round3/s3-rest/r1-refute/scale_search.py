#!/usr/bin/env python3
"""Necessary scale/trace diagnostic, NOT a lattice witness search certificate.

Models only scalar normalization factors and the actual su(2) trace pairing:
- chart toM2: lean/src/R2Coord.lean:19
- fibre inner: lean/src/AdalyFormal/Balaban/SuTwoInner.lean:104,483
- unit pair/mass/energy: AHP/round3/s3-rest/pin/Statement.lean:302,309,314,319
- frozen energy: lean/src/AdalyFormal/Balaban/RegularUPerturbation.lean:355
- Q1 normalization: lean/src/ZXR2Unit1.lean:70-77
- corridor matrix/inverse/lift: lean/src/ZXR2Unit2.lean:84-105
- frozen D2in: lean/src/ZXR2Wire2.lean:90-91
- linked raw/normalized scales: pin/Statement.lean:333,348,356,364,370,379
- finePair/J: pin/Statement.lean:51,148; final term: pin/Statement.lean:404

No invented Q, J, quadratic jet or H1 matrix is evaluated. The scalar test
assumes H1 identification and scalar inverse homogeneity, then searches for a
scale mismatch. It does not verify any admissible configuration or inverse.
Memory is O(1), a few dozen 2x2 matrices. No fine torus is allocated.
"""
import json
import random
from fractions import Fraction as F

rng = random.Random(20261021)

def chart(v):
    a,b,c = v
    return ((1j*a, b+1j*c), (-b+1j*c, -1j*a))

def trpair(x,y):
    return -0.5 * sum(x[i][j]*y[j][i] for i in range(2) for j in range(2)).real

max_trace_error = 0.0
for _ in range(1000):
    v = [rng.uniform(-3,3) for _ in range(3)]
    w = [rng.uniform(-3,3) for _ in range(3)]
    max_trace_error = max(max_trace_error, abs(trpair(chart(v),chart(w))-sum(a*b for a,b in zip(v,w))))

rows=[]
for ell in (2,3,5,13):
    for k in (2,3,5,12):
        eta=F(1,ell**k)
        for reading in ('raw','normalized'):
            # Printed Q = qscale * Q1; raw remainder = ell times normalized.
            qscale = F(ell) if reading == 'raw' else F(1)
            remscale = F(1) if reading == 'raw' else F(1,ell)
            lift_rem_scale = 1/qscale * remscale
            frozen_D2_scale = F(1,ell)
            nonlinear_ratio = frozen_D2_scale/(eta**3 * eta**(-3) * lift_rem_scale)
            rows.append(dict(ell=ell,k=k,reading=reading,nonlinear_ratio=str(nonlinear_ratio),mass_ratio='1',energy_ratio='1'))
            assert nonlinear_ratio == 1

# Rejected mutation: divide the remainder alone by ell, but keep the raw lift.
# This generates a mismatch, but is not either pinned UnitReading.
mutants = [{'ell':ell,'nonlinear_ratio':str(F(ell)),'admitted':False} for ell in (2,3,5,13)]
print(json.dumps(dict(scope='scalar/trace prefilter only; no actual configuration or jet search',cases=len(rows),max_trace_error=max_trace_error,linked_mismatches=0,rows=rows,rejected_one_sided_mutations=mutants,candidate=None),indent=2))
