#!/usr/bin/env bash
set -euo pipefail
cd /home/sebastian/BalabanCoercivityLemma
# Compact modules only. Never compile the historical Attempt on this worker.
python3 AHP/round10/assembly/r3/build.py
for f in \
  AHP/round10/assembly/r3/Neutral.lean \
  AHP/round10/assembly/r3/Compact.lean \
  AHP/round10/assembly/r3/JetCompact.lean \
  AHP/round10/shared/assembly/R3_NeutralResponse.lean \
  AHP/round10/shared/assembly/R3_EnergyGlue.lean \
  AHP/round10/shared/assembly/R3_JetGlue.lean; do
  AHP/round3/lean1.sh "$f"
done
python3 AHP/round10/assembly/r3/numerics/summarize.py
python3 AHP/round10/assembly/r3/audit.py
# The expensive numerical solves are deliberately not rerun here; see NOTES.md.
