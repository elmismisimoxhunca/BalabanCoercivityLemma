#!/usr/bin/env bash
# Sequential numerical batch; each job through the heavy scheduler.
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
run() {  # name, args...
  local name=$1; shift
  "$BB_CLI" heavy run -- python3 sepcheck.py "$@" > "$name.log" 2>&1
  echo $? > "$name.exit"
}
run sep_q2_R18_e1e-100_p500 --q 2 --R 18 --eps 1e-100 --dps 500 --iy 7 --iz 7
run sep_q2_R18_e1e-40_p400  --q 2 --R 18 --eps 1e-40  --dps 400 --iy 7 --iz 7
run sep_q2_R18_e1e-60_p400  --q 2 --R 18 --eps 1e-60  --dps 400 --iy 7 --iz 7
run sep_q2_R18_e1e-6_p300   --q 2 --R 18 --eps 1e-6   --dps 300 --iy 7 --iz 7
run sep_q1_R18_e1e-40_p200  --q 1 --R 18 --eps 1e-40  --dps 200 --iy 0 --iz 0
run sep_q2_R20_e1e-100_p450 --q 2 --R 20 --eps 1e-100 --dps 450 --iy 7 --iz 7
echo done > batch1.done
