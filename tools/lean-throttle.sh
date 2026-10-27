#!/usr/bin/env bash
# Wrapper around the real `lean` binary, used via the LEAN environment variable so that Lake's
# many parallel jobs never exceed LEAN_MAX_PROCS compiler processes.  Only invocations that
# compile a .lean file are throttled; queries such as `lean --version` pass straight through.
#   LEAN_REAL           path of the real lean binary (required)
#   LEAN_CHILD_THREADS  value of LEAN_NUM_THREADS given to each compile (default 1)
#   LEAN_MAX_PROCS      concurrent compile slots (default 2)
#   LEAN_MACHINE_MAX    also wait while `pgrep -c -x lean` >= this (default 6; 0 = off)
#   LEAN_MIN_AVAIL_GB   also wait while available RAM is below this many GB (default 8; 0 = off)
real="${LEAN_REAL:?LEAN_REAL not set}"
compile=0
for a in "$@"; do case "$a" in *.lean) compile=1;; esac; done
[ "$compile" = 1 ] || exec "$real" "$@"
n="${LEAN_MAX_PROCS:-2}"
mm="${LEAN_MACHINE_MAX:-6}"
ma="${LEAN_MIN_AVAIL_GB:-8}"
dir="${LEAN_SLOT_DIR:-${TMPDIR:-/tmp}/adaly-lean-slots-$(id -u)}"
mkdir -p "$dir"
while true; do
  for i in $(seq 1 "$n"); do
    exec {fd}>"$dir/slot$i"
    if flock -n "$fd"; then
      # slot acquired; now check machine-wide limits
      if [ "$mm" != 0 ] && [ "$(pgrep -c -f "^${real} ")" -ge "$mm" ]; then :
      elif [ "$ma" != 0 ] && [ "$(free -g | awk '/^Mem:/{print $7}')" -lt "$ma" ]; then :
      else
        LEAN_NUM_THREADS="${LEAN_CHILD_THREADS:-1}" "$real" "$@"; rc=$?
        exec {fd}>&-
        exit $rc
      fi
      flock -u "$fd"
    fi
    exec {fd}>&-
  done
  sleep $((5 + RANDOM % 5))
done
