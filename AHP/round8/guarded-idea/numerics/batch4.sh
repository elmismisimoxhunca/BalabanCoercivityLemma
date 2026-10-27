#!/usr/bin/env bash
# Direct separation checks at larger R inside the vacuum window; after the q=4 run.
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
while [ ! -f sep_q4_R18_e1e-170_p480.exit ]; do sleep 30; done
run() {  # name, args...
  local name=$1; shift
  "$BB_CLI" heavy run -- python3 sepcheck.py "$@" > "$name.log" 2>&1
  echo $? > "$name.exit"
}
run sep_q2_R24_e1e-140_p450 --q 2 --R 24 --eps 1e-140 --dps 450 --iy 7 --iz 7
run sep_q2_R30_e1e-170_p460 --q 2 --R 30 --eps 1e-170 --dps 460 --iy 7 --iz 7
echo done > batch4.done
