#!/usr/bin/env bash
# q=4 vacuum all-sector screen; starts after batch2 has finished.
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
while [ ! -f batch2.done ]; do sleep 30; done
"$BB_CLI" heavy run -- python3 screen.py 4 18 0.5593 0.55935 0.5594 > screen_q4_R18.log 2>&1
echo $? > screen_q4_R18.exit
echo done > batch3.done
