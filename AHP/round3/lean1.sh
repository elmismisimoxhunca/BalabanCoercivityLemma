#!/usr/bin/env bash
# Compile one Lean file, at most SLOTS at a time across all AHP workers.
# SLOTS: 1 on 16 GB (until 2026-10-23), 4 on 78 GB, back to 2 on 16 GB (2026-10-23).
# Usage: AHP/round3/lean1.sh <file.lean>   writes <file.lean>.log and <file.lean>.exit
set -u
f="$(realpath "$1")"
export PATH="$HOME/.elan/bin:$PATH"
cd /home/sebastian/BalabanCoercivityLemma/lean
SLOTS=2
LOCKDIR=/home/sebastian/BalabanCoercivityLemma/AHP/round3
while :; do
  for i in $(seq 0 $((SLOTS - 1))); do
    exec 9>"$LOCKDIR/.lean.lock.$i"
    if flock -n 9; then
      lake env lean "$f" > "$f.log" 2>&1
      rc=$?
      echo "$rc" > "$f.exit"
      exit "$rc"
    fi
    exec 9>&-
  done
  sleep 5
done
