#!/usr/bin/env python3
"""Reflection check for `eventually_pathSeparation_of_coupling` (numerical evidence only).

Reflecting the interior profile f -> -f is the same as reflecting the curvature
eps -> -eps (Lean: pathA_neg, pathD_neg).  The first-order coupling is linear in the
profile, so the round-8 post-crossing separation of the defect-line family (c1 < 0 at
q = 2) must turn into a PRE-crossing separation (corrected crossing before the carrier
crossing, carrier positive definite there) for the reflected profile.

This runs the round-8 exact boundary-Schur separation check (sepcheck.run, which imports
the round-6 probe transcription read-only) at negative curvature and writes its JSON into
this directory only (sepcheck.OUTDIR is redirected before the run; no bytecode is
written).  No interval arithmetic, no certified enclosure.
"""
import os
import sys
sys.dont_write_bytecode = True
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
sys.path.insert(0, '/home/sebastian/BalabanCoercivityLemma/AHP/round8/guarded-idea/numerics')
import argparse
from pathlib import Path
import sepcheck  # noqa: E402

HERE = Path(__file__).resolve().parent
sepcheck.OUTDIR = HERE / 'out'
sepcheck.OUTDIR.mkdir(exist_ok=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--q', type=int, default=2)
    p.add_argument('--R', type=int, default=18)
    p.add_argument('--eps', default='-1e-100')
    p.add_argument('--dps', type=int, default=400)
    p.add_argument('--iy', type=int, default=7)
    p.add_argument('--iz', type=int, default=7)
    a = p.parse_args()
    sepcheck.run(a.q, a.R, a.eps, a.dps, a.iy, a.iz, tag='_reflected')
