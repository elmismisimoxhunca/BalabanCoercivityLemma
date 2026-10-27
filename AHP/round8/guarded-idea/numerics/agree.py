#!/usr/bin/env python3
"""Relative agreement (decimal digits) between two independent-precision runs."""
import json, sys
import mpmath as mp
mp.mp.dps = 1200
a, b = (json.load(open(f)) for f in sys.argv[1:3])
keys = ['tB1', 'tC1', 'tC1_minus_tB1', 'tB2_minus_tB1', 'unit_kernel_pairing', 'first_order_shift']
out = {}
for k in keys:
    x, y = mp.mpf(a[k]), mp.mpf(b[k])
    out[k] = float(-mp.log10(abs(x - y) / abs(y))) if x != y else float('inf')
for k in ['A_boundary_spectrum_at_tC1']:
    for i in range(2):
        x, y = mp.mpf(a[k][i]), mp.mpf(b[k][i])
        out[f'{k}[{i}]'] = float(-mp.log10(abs(x - y) / abs(y)))
print(json.dumps(out, indent=1))
