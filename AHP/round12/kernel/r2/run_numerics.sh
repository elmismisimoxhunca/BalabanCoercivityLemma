#!/usr/bin/env bash
set -u
cd /home/sebastian/BalabanCoercivityLemma
export PATH="/home/sebastian/.bb-machines/bb-s6.mesh.srtv.cl/runtime/node_modules/bb-app/host-daemon/dist:$PATH"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
for precision in 120 155; do
  file="AHP/round12/kernel/r2/star_right_q2_R20_p${precision}"
  bb heavy run -- python3 AHP/round12/kernel/r2/star_crosscheck.py --side right --dps "$precision" > "${file}.log" 2>&1
  code=$?
  printf '%s\n' "$code" > "${file}.exit"
  printf 'PRECISION %s EXIT %s\n' "$precision" "$code"
  if [ "$code" != 0 ]; then exit "$code"; fi
done
