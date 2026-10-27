# S-2 non-vacuity — round 1, refute

## Result and stopping boundary

**Closed goal: `AdalyFormal.AHP.Round2.S2Nonvacuity.GoalNeg2`.**

Main declaration: `AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved`,
[Attempt.lean:519](Attempt.lean#L519). Its type is exactly `GoalNeg2`, with no
additional hypothesis. Thus every **corner-class** member covered by the
pinned headline side conditions has base domain empty or the whole fine
torus. `not_goalPos2` (line 524) also excludes the pinned cofinal positive
corner-family goal.

This is **partial progress on the item**, not closure of S-2 non-vacuity:
`GoalPos1` and `GoalNeg1` for the **four-bond class** remain unproved here.
Nothing identifies the class with the printed regularity class, changes the
operators, proves an analytic inequality, or refutes Balaban's printed lemma.

## Numerics first

Ran `python3 -B numerics.py` before constructing the Lean attempt. The script
has a 3.5-billion-byte address-space limit, uses only the standard library,
and cites the Lean file and declaration line of every modelled predicate.
It models geometry only, not a gauge operator or an admissible headline
instance. Output is [numerics.json](numerics.json); [numerics.exit](numerics.exit)
is 0. Counts are exact integers, with no numerical tolerance.

- All 254 proper nonempty subsets of the side-2 torus failed one-corner
  coverage even when the possible witnesses were relaxed to **all** contained
  product boxes, not only the frozen class cubes.
- On sides 4 and 5 the domain `[0,2)^3` has the exit square with corners
  `(1,0,0), (2,0,0), (1,1,0), (2,1,0)`.
- On side 8 the domain `[0,4)^3` has the exit square with corners
  `(3,0,0), (4,0,0), (3,1,0), (4,1,0)`.
- The corner memberships are `[true,false,true,false]`. Among respectively
  9, 9, and 100 nonempty contained boxes, **zero** touch all four edges.
  All three squares satisfy the corner antecedent and **fail the four-bond
  antecedent**. These are not factor-12 headline instances.

This supplies a candidate obstruction, not the universal conclusion. The
Lean proof generalizes the exit-square obstruction to every proper nonempty
admissible tower, rather than promoting the finite scan into a theorem.

## Explicit counterexample and proof route

The pinned negative goal is universal saturation, not an existential
counterexample to coercivity. The explicit counterexample below is to the
**coverage obligation on any proposed proper nonempty domain**.

1. A product `siteBox` that touches all four edges of a plaquette contains
   all four corners (`touchCover_all_corners`, line 371). Its vertex cover
   contains an opposite pair; product membership fills in the other pair.
   These helpers are copied verbatim from the compiled Stage-B file.
2. Every frozen class cube is a subset of `S.Om 0` on an admissible tower
   (`class_sites_subset_om0`, line 413). This uses the actual two-stratum
   clause and frozen `StatementLaneR8.admissible_mono`, not an assumed
   enlargement of the cube family.
3. A proper nonempty subset has an exit bond (`exists_exit`, line 454).
   The finite-torus connectivity proof uses `shift_iter` and
   `forall_of_shift`, copied verbatim from frozen `lean/src/CvN4.lean:36–61`.
   That module is not imported; only its two proofs are copied.
4. **`explicit_exit_square`, line 468**, constructs the square at the inside
   endpoint of that bond: directions `(0,1)` for exit direction 0 or 1,
   and `(0,2)` for exit direction 2. Its base corner is inside. No frozen
   class cube can touch all four edges, because step 1 would put the outside
   endpoint into the cube and step 2 would put it back in the domain.
5. **`proper_domain_uncovered`, line 488**, supplies such an uncovered
   corner plaquette on every proper nonempty admissible tower. The purported
   `CoversPlaqCorner` witness contradicts it. This proves `corner_saturation`
   (line 506), hence the exact pinned `GoalNeg2` (line 519).

The stronger geometry lemma needs neither a lower bound on M nor TorusOK,
positive alpha, or regularity. These are not removed from the pinned goal;
its full binder sequence is retained verbatim and the theorem specializes
the stronger lemma to it. The main proof actually uses the explicit
uncovered-plaquette route. `corner_coverage_shift_closed` (line 438) records
an additional equivalent propagation mechanism.

## Compilation and exact-statement audit

Only frozen imports `ZT5A` and `ZR8Class` are used. No AHP import occurs.
All 14 pinned definitions, including both classes, both `Proper*At`
propositions and all four goal propositions, were copied **character for
character**. The four corner definitions are likewise verbatim Stage-B
copies; no placeholder operator is introduced.

Final command, run serially from the frozen project's directory:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean.log 2>&1
echo $? > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean.exit
```

[Final exit](Attempt.lean.exit): **0**. [Full log](Attempt.lean.log): no
warnings or errors; **48 axiom records**, covering all **45 local
declarations** and three directly used frozen helpers. Every list is a
subset of `propext`, `Classical.choice`, `Quot.sound`.

Main record:

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source SHA-256:
`c4a1d4d0614dd1fcf700219fbd12fd03349a4b7f600dea0da15d678dfb553ccd`.

`python3 -B audit.py` checks the exit record, all 14 exact definition copies,
the copied corner definitions/connectivity proofs, main type output, axiom
allowlist, every local declaration's print, sole frozen imports, and a
full-source forbidden-token scan. [AUDIT.json](AUDIT.json) records all checks
passing; [audit.exit](audit.exit) is 0. This is a self-audit, not an independent
verifier's report.

Development: the direct shift-closure proof compiled first. While making
the actual uncovered plaquette explicit, one compilation failed because
`Set.ne_univ_iff_exists_not_mem` is not available in the frozen environment.
It was replaced with a short contradiction using `Set.eq_univ_of_forall`.
The final complete source then compiled successfully and was compiled again
after adding the exact main-type check. No failed compilation is counted as
evidence; only the current successful source and log are accepted.

## Why this attempt stops here

The requested one-negative-goal target has been met for the corner class.
The exit squares are **not** four-touch plaquettes in the numerical product
domains; consequently their noncoverage cannot contradict
`CoversPlaqFour`. The inclusion chain from Stage B does not reverse, so the
corner saturation theorem cannot be transferred to the four-bond class.
A separate proper-domain four-bond witness or a different universal
obstruction is still needed to close the item. The evidence here supports
neither a proof nor a refutation of `GoalNeg1`.

All authored files are confined to `AHP/round2/s2-nonvacuity/r1-refute/`.
No build/update/reproduction command, commit, push, removal, or edit to the
protected tree was performed. Pre-existing shared-checkout changes to the
lakefile and compact-module directories were not touched.
