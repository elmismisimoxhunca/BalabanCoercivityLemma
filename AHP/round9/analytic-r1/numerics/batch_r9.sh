#!/usr/bin/env bash
# Sequential round-9 numerics (one heavy slot).  Run from this directory via
#   "$BB_CLI" heavy run -- bash batch_r9.sh
set -u
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
# dictionary check at q = 8 (first sector m = -3 -> character 4q-3 = 29)
python3 actual_check.py --q 8 --R 2 --iy 29 --iz 29 --dps 50
# first sector at larger scales
for q in 64 128 256; do python3 firstsector.py --q $q --width 2; done
# K along the diagonal near the continuum minimiser, and off-diagonal neighbours
python3 kscan.py --R 6 --dps 50 --ks=-0.36,-0.32,-0.30,-0.28,-0.267,-0.25,-0.23,-0.21,-0.18,-0.15
python3 kscan.py --R 6 --dps 50 --ks=-0.30:-0.24,-0.24:-0.30,-0.32:-0.22,-0.22:-0.32
# R-independence of K at k = -pi/8 (q = 1 geometry): R = 8, 10
python3 kscan.py --R 8 --dps 60 --ks=-pi/8
python3 kscan.py --R 10 --dps 70 --ks=-pi/8
echo BATCH_DONE
