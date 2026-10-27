#!/usr/bin/env bash
set -u
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 actual_check.py --q 8 --R 2 --iy 29 --iz 29 --dps 80
python3 kscan.py --R 16 --dps 80 --ks=-pi*3/32
python3 actual_check.py --q 4 --R 2 --iy 15 --iz 15 --dps 60
python3 actual_check.py --q 8 --R 2 --iy 28 --iz 28 --dps 80
echo BATCH_DONE
