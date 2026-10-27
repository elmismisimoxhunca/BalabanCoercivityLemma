#!/usr/bin/env bash
# Reproduce the machine check from a fresh clone:
#   1. toolchain (Lean v4.31.0 via elan)      2. mathlib sources at the pinned revision + prebuilt cache
#   3. lake build of every module              4. Check.lean (#print axioms of every CLAIMS declaration)
#   5. validate complete (possibly wrapped) axiom records and compare with expected/axioms.expected.txt
#
# Environment knobs (all optional):
#   MAX_LEAN=2          maximum concurrent lean compile processes (default 2)
#   LEAN_NUM_THREADS=1  threads per lean process (default 1)
#   MIN_AVAIL_GB=8      do not start a compile while less RAM than this is available (0 = off)
#   MACHINE_LEAN_MAX=6  do not start a compile while this many lean processes already run (0 = off)
#   PACKAGES_FROM=DIR   offline mode: copy the package directories (mathlib, batteries, ...) from DIR
#                       (a .lake/packages directory of a mathlib v4.31.0 build) instead of cloning
#                       from GitHub and downloading the cache.  DIR must contain built oleans.
#   SKIP_BUILD=1        skip step 3 (only run Check and the comparison)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT/lean"
LOG="$ROOT/reproduce.log"; : > "$LOG"
say() { echo "[$(date +%H:%M:%S)] $*" | tee -a "$LOG"; }
fail() { say "FAIL: $*"; exit 1; }

# ---- 1. toolchain
command -v elan >/dev/null || fail "elan not found (install from https://github.com/leanprover/elan)"
TC="$(cat lean-toolchain)"; say "toolchain pin: $TC"
PREFIX="$(elan run --install "$TC" lean --print-prefix 2>>"$LOG")" || fail "cannot install/locate toolchain $TC"
LAKE_BIN="$PREFIX/bin/lake"; LEAN_BIN="$PREFIX/bin/lean"
[ -x "$LAKE_BIN" ] && [ -x "$LEAN_BIN" ] || fail "cannot locate lake/lean under $PREFIX"
export PATH="$PREFIX/bin:$PATH"
say "lean: $("$LEAN_BIN" --version)"

# ---- throttle: Lake starts as many lean processes as the dependency graph allows and has no job
# limit.  We build a private copy of the toolchain's bin/ directory in which `lean` is a wrapper
# (tools/lean-throttle.sh) that admits at most MAX_LEAN concurrent compiles; Lake finds its lean
# relative to its own location, so it uses the wrapper.
SYSROOT="$ROOT/.sysroot"; rm -rf "$SYSROOT"; mkdir -p "$SYSROOT/bin"
for b in "$PREFIX"/bin/*; do ln -s "$b" "$SYSROOT/bin/$(basename "$b")"; done
rm "$SYSROOT/bin/lake" "$SYSROOT/bin/lean"; cp "$PREFIX/bin/lake" "$SYSROOT/bin/lake"
printf '#!/usr/bin/env bash\nexec "%s/tools/lean-throttle.sh" "$@"\n' "$ROOT" > "$SYSROOT/bin/lean"; chmod +x "$SYSROOT/bin/lean"
for d in lib include share src; do [ -e "$PREFIX/$d" ] && ln -s "$PREFIX/$d" "$SYSROOT/$d"; done
LAKE="$SYSROOT/bin/lake"
export LEAN_REAL="$LEAN_BIN"
export LEAN_MAX_PROCS="${MAX_LEAN:-2}" LEAN_MIN_AVAIL_GB="${MIN_AVAIL_GB:-8}" LEAN_MACHINE_MAX="${MACHINE_LEAN_MAX:-6}"
export LEAN_CHILD_THREADS="${LEAN_NUM_THREADS:-1}" MIMALLOC_ARENA_RESERVE=0 LC_ALL=C
unset LEAN_NUM_THREADS   # must not reach Lake itself: it would serialise all jobs

# ---- 2. packages + cache
if [ -n "${PACKAGES_FROM:-}" ]; then
  say "offline mode: copying packages from $PACKAGES_FROM"
  mkdir -p .lake/packages
  for p in "$PACKAGES_FROM"/*; do
    n="$(basename "$p")"; [ "$n" = Cli ] && continue
    [ -e ".lake/packages/$n" ] || cp -a "$p" ".lake/packages/$n" || fail "copy $n"
  done
else
  say "fetching packages and mathlib cache (network)"
  "$LAKE" exe cache get >>"$LOG" 2>&1 || fail ""$LAKE" exe cache get (see reproduce.log); try PACKAGES_FROM for offline mode"
fi

# ---- 3. build
if [ "${SKIP_BUILD:-0}" != 1 ]; then
  say "lake build (MAX_LEAN=$LEAN_MAX_PROCS, threads/process=$LEAN_CHILD_THREADS); this takes many hours on a cold tree"
  t0=$(date +%s)
  "$LAKE" build >>"$LOG" 2>&1; rc=$?
  say "lake build exit=$rc after $(( $(date +%s) - t0 )) s"
  [ $rc = 0 ] || fail "lake build failed (see reproduce.log)"
fi
NMOD=$(tail -n +2 MODULES.tsv | wc -l)
say "modules in project: $NMOD"

# ---- 4./5. axiom checks and comparison with the expected files
# Check1..CheckN together cover every CLAIMS declaration (split because modules of different lanes
# declare the same names and cannot share one environment); CheckR7 is the old-statement cone.
STATUS=0
run_check() {  # $1 = file stem
  "$LAKE" env "$LEAN_BIN" "$1.lean" > "$ROOT/$1.raw" 2>&1; rc=$?
  if [ $rc != 0 ] || grep -q "error" "$ROOT/$1.raw"; then say "FAIL: errors in $1.lean (see $1.raw)"; return 1; fi
  if ! python3 "$ROOT/tools/check_axioms.py" "$ROOT/$1.raw" --output "$ROOT/$1.axioms.txt"; then
    say "FAIL: incomplete or forbidden axioms in $1 output"; return 1
  fi
  say "$1.lean exit=$rc; complete axiom records: $(wc -l < "$ROOT/$1.axioms.txt")"
  return 0
}
: > "$ROOT/Check.axioms.txt"
for f in $(ls Check[0-9]*.lean | sort -V); do
  run_check "${f%.lean}" || STATUS=1
  if [ -f "$ROOT/${f%.lean}.axioms.txt" ]; then
    cat "$ROOT/${f%.lean}.axioms.txt" >> "$ROOT/Check.axioms.txt"
  fi
done
run_check CheckR7 || STATUS=1
for pair in "Check:axioms.expected.txt" "CheckR7:axioms.r7.expected.txt"; do
  stem="${pair%%:*}"; exp="$ROOT/expected/${pair##*:}"
  if diff -u "$exp" "$ROOT/$stem.axioms.txt" > "$ROOT/$stem.diff"; then
    say "PASS: $stem axiom output identical to $(basename "$exp") ($(wc -l < "$ROOT/$stem.axioms.txt") lines)"
  else
    say "FAIL: $stem axiom output differs from $(basename "$exp") (see $stem.diff)"; STATUS=1
  fi
done
# ---- 6. forbidden-token scan (sorry, admit, native_decide, axiom, unsafe, ...) over lean/src
python3 "$ROOT/tools/scan_forbidden.py" > "$ROOT/forbidden_tokens.txt"
if diff -u "$ROOT/expected/forbidden_tokens.expected.txt" "$ROOT/forbidden_tokens.txt" > "$ROOT/forbidden_tokens.diff"; then
  say "PASS: forbidden-token scan equals expected list ($(wc -l < "$ROOT/forbidden_tokens.txt") modules; see HANDOFF.md)"
else say "FAIL: forbidden-token scan differs (see forbidden_tokens.diff)"; STATUS=1; fi
[ $STATUS = 0 ] && say "ALL CHECKS PASSED" || say "SOME CHECKS FAILED"
exit $STATUS
