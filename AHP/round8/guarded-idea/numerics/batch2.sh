#!/usr/bin/env bash
# Vacuum coefficients; starts after batch1 has finished (one heavy slot at a time).
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
while [ ! -f batch1.done ]; do sleep 30; done
run() {  # name, args...
  local name=$1; shift
  "$BB_CLI" heavy run -- python3 vacuum_coeff.py "$@" > "$name.log" 2>&1
  echo $? > "$name.exit"
}
run vac_q2_R18_p340 --q 2 --R 18 --dps 340 --iy 7 --iz 7
run vac_q2_R20_p400 --q 2 --R 20 --dps 400 --iy 7 --iz 7
run vac_q2_R24_p400 --q 2 --R 24 --dps 400 --iy 7 --iz 7
run vac_q2_R30_p400 --q 2 --R 30 --dps 400 --iy 7 --iz 7
run vac_q1_R18_p200 --q 1 --R 18 --dps 200 --iy 0 --iz 0 --lo 0.55 --hi 0.62
run vac_q4_R18_p520 --q 4 --R 18 --dps 520 --iy 15 --iz 15
echo done > batch2.done
