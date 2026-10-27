#!/usr/bin/env bash
set -u
export PATH=/home/sebastian/.bb-machines/bb-s6.mesh.srtv.cl/runtime/node_modules/bb-app/host-daemon/dist:$PATH
cd /home/sebastian/BalabanCoercivityLemma
base=AHP/round12/kernel/r1
for d in 190 230; do
  bb heavy run -- python3 "$base/crosscheck.py" precise --dps "$d" > "$base/precise_p$d.log" 2>&1
  code=$?
  printf '%s\n' "$code" > "$base/precise_p$d.exit"
  if [ "$code" != 0 ]; then exit "$code"; fi
done
for args in '0 0 1' '1 1 1' '0 0 0'; do
  read -r iy iz charge <<< "$args"
  name="competitor_s${iy}_${iz}_c${charge}_p80"
  bb heavy run -- python3 "$base/crosscheck.py" precise --competitor --dps 80 --iy "$iy" --iz "$iz" --charge "$charge" > "$base/$name.log" 2>&1
  code=$?
  printf '%s\n' "$code" > "$base/$name.exit"
  if [ "$code" != 0 ]; then exit "$code"; fi
done
printf 'NUMERICS_COMPLETE\n'
