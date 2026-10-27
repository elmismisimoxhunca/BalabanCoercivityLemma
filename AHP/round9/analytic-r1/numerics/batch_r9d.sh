#!/usr/bin/env bash
set -u
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 screen_left.py 2 18 0.5639 0.56397151 0.5641 > screen_left_q2_R18.log 2>&1; echo $? > screen_left_q2_R18.exit
python3 screen_left.py 4 18 0.5593 0.55934749 0.5594 > screen_left_q4_R18.log 2>&1; echo $? > screen_left_q4_R18.exit
echo BATCH_DONE
