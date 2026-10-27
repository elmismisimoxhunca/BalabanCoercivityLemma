#!/usr/bin/env bash
set -u
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
# left-only twist on the actual q = 8 geometry at modest precision (no near-degeneracy expected)
python3 lefttwist.py --R 2 --dps 50 --q 8 --iy 29 --iz 29
python3 lefttwist.py --R 2 --dps 50 --q 2 --iy 7 --iz 7
python3 lefttwist.py --R 2 --dps 50 --q 4 --iy 15 --iz 15
# left-only twist: K along the diagonal (q = 1 geometry, R = 6)
python3 lefttwist.py --R 6 --dps 50 --ks=-pi/16,-pi*3/32,-0.267,-pi/8,-0.15
echo BATCH_DONE
