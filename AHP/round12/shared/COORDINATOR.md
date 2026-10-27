# Coordinator notes, round 12

## Round-10 assembly compiled on 78 GB (2026-10-24)

`AHP/round10/assembly/r4/Attempt.lean` was copied byte-for-byte to `Attempt.coord.lean` and compiled once with `AHP/round3/lean1.sh` while the machine had 78 GB. It ran to completion in 585 s with no memory kill, so **memory is no longer the blocker for that file**.

Result: **exit 1, 4 errors**, all in the appended Color/ColorResponse section:

- line 16148 `Unknown identifier half_twice`
- line 16177 `Unknown identifier half_average`
- line 16188 `Unknown identifier phase_axis_fixed` (and an unsolved goal at 16186)

These helpers exist in `shared/dictionary/R4_ColorResponse.lean` (:1376, :1467, :1480) and in the R3 dictionary files, but were not copied into the concatenation. 1179 axiom lines were printed; 15 are non-standard (sorryAx from the failing declarations and their dependants). Log: `AHP/round10/assembly/r4/Attempt.coord.lean.log`.

Consequences:
1. The round-10 joins are **assembled but broken (missing helper copies)**, not merely memory-blocked. The blueprint must record them in that category.
2. Fixing them is mechanical: copy the three helpers (and anything they need) into the concatenation before the Color section. Do not do this in the round-10 directory; do it in an AHP/round12 copy if your track needs a compiled join.
3. While RAM is 78 GB, lean1.sh still limits to 2 concurrent jobs; a large file takes about 10 minutes.
