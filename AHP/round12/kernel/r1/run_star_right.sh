#!/usr/bin/env bash
set -u
export PATH=/home/sebastian/.bb-machines/bb-s6.mesh.srtv.cl/runtime/node_modules/bb-app/host-daemon/dist:$PATH
cd /home/sebastian/BalabanCoercivityLemma
base=AHP/round12/kernel/r1
for d in 90 120; do
  bb heavy run -- python3 "$base/star_crosscheck.py" --side right --dps "$d" > "$base/star_right_q1_R20_p$d.log" 2>&1
  code=$?
  printf '%s\n' "$code" > "$base/star_right_q1_R20_p$d.exit"
  if [ "$code" != 0 ]; then exit "$code"; fi
done
printf 'STAR_RIGHT_COMPLETE\n'
