#!/usr/bin/env bash
# Independent byte-copy replay. The shared wrapper owns locking and heavy slots.
set -u
cd /home/sebastian/BalabanCoercivityLemma
rc=0
for name in pin r1-prove r1-refute r2-prove r2-refute r3-prove r3-refute; do
  file="AHP/round3/guarded/judge/$name.lean"
  printf '%s START %s\n' "$(date -Is)" "$name"
  LEAN_NUM_THREADS=1 AHP/round3/lean1.sh "$file"
  status=$?
  printf '%s END %s exit=%s\n' "$(date -Is)" "$name" "$status"
  if [ "$status" -ne 0 ]; then rc=1; fi
done
printf '%s\n' "$rc" > AHP/round3/guarded/judge/recheck.exit
exit "$rc"
