# S-1, round 1, positive attempt

## Result

**Closed exactly as pinned: `Round2.S1.GoalPos2`**, by
`Round2.S1.goalPos2_proved`, `Attempt.lean:689`.

Also proved the exact primary goal `Round2.S1.GoalPos1`, by
`Round2.S1.goalPos1_proved`, `Attempt.lean:575`.

The reduced goal includes **both** the coverage-collapse theorem and the
changed-operator headline equivalence. No hypothesis was added to either goal.
All 22 definitions/goal wrappers from `../pin/Statement.lean` are copied
byte-for-byte, including the unused shell fallback and negative-goal wrappers.

**Material limit:** this is a result for the explicitly coverage-repaired pin,
not certification of Balaban's unmodified touching convention. Common-cube
corner coverage, together with frozen product-box class cubes in a nested
tower, forces the base domain to be empty or the whole torus. It excludes every
proper nonempty slab regardless of its link phases. This is a consequence of
the added coverage hypothesis, not of the quoted endpoint/corner convention
alone. No result here proves `GoalPos3` / `P428Target8Shell`, reverse inclusion
of the two regularity classes, or non-flat richness of the remaining class.

## Proof route and reuse

The nearest frozen theorem is
`AdalyFormal.M2RightInv.p428Target8`, `lean/src/RI6.lean:323`.
Rather than rebuilding its analytic proof, the attempt reuses it after
proving that the pin's apparent operator change disappears on its class.

1. **One cube contains the whole square.** The Stage-B S-2 square/product-box
   helpers are copied into this standalone file (`Attempt.lean:238–470`;
   no AHP import). A vertex cover of a four-cycle contains an opposite pair;
   a product box containing that pair contains all four corners. Thus a
   corner-covered plaquette has every boundary bond as a frozen `CubeBond`
   in its covering cube (`corner_cover_inside`, line 486).
2. **Selector equality from coverage.** The two containment helpers at lines
   472 and 477 copy the frozen proofs from `D1Final.lean:31–43`.
   On a nested tower every class cube lies in `S.Om 0`. Consequently
   `corner_eq_inside_of_coverage` (line 501) proves
   `plaqCorner (S.Om 0) = plaqIn (S.Om 0)` for *any* cube factor and lattice;
   no smallness, radius, or torus-size premise is needed.
3. **Class transfer includes every guard.** `PerCubeRegularTouch.toFrozen`
   (line 458) transfers pointwise, forward-difference, and both curl guards,
   preserving each per-cube gauge and logarithm. The coverage transfer and
   `ClassCoupledCorner.toFrozen` are at lines 514 and 519.
4. **Actual operator chain.** `dataS_congr_at` (line 527) handles selected
   Delta and J together. `G1invS_congr_at` (line 532) propagates equality
   through the chosen corrected inverse operator. `genFormS_congr_at`
   (line 539) propagates it through Nmat, totalised inversion, firstTerm,
   H1in, and the nonlinear J term. `instIneq_corner_iff_of_eq` (line 546)
   uses frozen `D1Literal.pin_genForm`, `D1Lit.lean:138`, to identify the
   resulting full form with the frozen one. This is equality of the actual
   full form on all its arguments, not a raw-Delta surrogate or a guarded
   comparison. No invertibility assumption is introduced.
5. **Primary headline.** `touchConsistent_of_frozen` (line 560) keeps the
   frozen theorem's entire quantifier order, thresholds, positive constants,
   cap, and `SidePow6` conjunct. It applies steps 2–4 at each instance.
   `goalPos1_proved` is its application to the existing frozen headline.
6. **Universal collapse.** Selector equality propagates membership along
   every positive coordinate shift (lines 579 and 595). The imported frozen
   transitivity theorem `U1AnchorPoincare.eq_of_shiftInvariant`
   (`lean/src/AdalyFormal/Balaban/U1AnchorPoincare.lean:130`) makes the Bool
   membership function constant. `extreme_of_selector_eq` (line 605) and
   `coverage_collapse_nested` (line 622) therefore prove empty/full collapse.
   The exact pinned `TouchCoverageCollapse` is proved at line 628. No claim
   requires all higher tower domains to be empty or full.
7. **Reduced headline equivalence.** On an extreme base,
   `instIneq_corner_iff_extreme` (line 647) proves the instance equivalence
   without a class or inverse-unit premise. `touchConsistent_of_extreme`
   (line 669) uses actual collapse, class inclusion, and this equality to
   turn the frozen extreme-base headline into the primary headline.
   The other direction uses `target8Extreme_of_frozen` (line 656) applied
   to the already proved frozen theorem, as expressly permitted by PIN.md.
   It is **not** a reverse class-inclusion theorem. The headline equivalence
   is at line 684; the exact conjunction `GoalPos2` is at line 689.

## What was tried, and why work stopped

The first route was local coverage-to-selector equality, which avoids needing
connectivity before proving the primary headline. That route compiled on the
first attempt. The explicit collapse and reduced-equivalence route then reused
the frozen periodic-shift transitivity theorem instead of introducing a new
path construction.

An intermediate compilation failed only in the empty-base selector lemma:
expanding the boundary finset under `simp` left an existential finset-membership
goal. Taking its explicit AB boundary edge resolved the empty case. A later
unnecessary-`simpa` warning was removed. The final file compiles without
warnings or errors; no failed proof placeholder remains.

Work stopped because both exact positive targets above are proved and checked.
No new analytic estimate or phase search is needed for this collapsed class.
The shell fallback still has proper domains and genuinely changed selectors,
so these proofs do not settle it. Deciding a non-collapsing printed-domain
reading needs a different, explicitly approved coverage pin, not a silent
change to this one. No numerical script was written or run.

## Print-fidelity ledger

This ledger retains the complete list in `../pin/PIN.md`, “Departures from the
print and retained readings.” That pin is the source-reading record; this
attempt read the mandated project records but did not claim a fresh independent
page-image audit. Proofs do not certify any of the unresolved source readings.

| Place | Pinned choice / departure, and why it stays |
|---|---|
| Coverage (principal issue) | Site coverage plus four touching boundary bonds of every one-corner plaquette in **one** factor-12 class cube. This common-cube clause is additional, not in the quoted CMP102 convention. It is retained because it is the immutable pin; its empty/full collapse is now proved. |
| Delta and J | Both use `selCorner`, via genuine `D1Lit.InstIneqS`. This applies the endpoint/corner convention to a domain-boundary reading; it is not the unrestricted torus sum displayed in (3.10)/(3.11). On this pin's class the selectors are now proved equal to frozen `plaqIn`. |
| Class guards | `TouchBond` replaces `CubeBond` in every pointwise and difference guard; `CurlReadsTouch` replaces all curl guards. Stencil-interior guards and cube-specific global extensions of gauge/logarithm remain formal treatments of “on the cube”; the quotation supplies no boundary extension law. |
| Cubes/factors | Frozen aligned periodic product boxes, unique index, adjacent-stratum containment, and one global factor 12 remain. The print describes block unions and cube-attached O(1). Product structure is essential to the proof; no union-class transfer is claimed. |
| Dimension/group | Three dimensions and SU(2), as in the frozen model; no general-dimension or general-group assertion. |
| Lattice/distance | Finite periodic rectangular tori, side-minus-one extents, divisibility, periodic l1 distance, eta = ell to minus k. These isolate S-1 in the frozen setting rather than deriving these conventions from the local printed claim. |
| Tower/base | Frozen strict collars, aligned half-open block unions, empty padding, exact p.396 RM block layer, and reading A of the fine lattice remain. No thinner-layer, alternative reading B, or p.408 third-enlargement condition is substituted. |
| Parameter ranges | All natural ell at least 2, a positive, k at least 1, M = ell^m with m at least 1, and all natural radii beyond threshold. Printed odd-L or power-of-L radius readings are not imposed. |
| Constants/order | Radius threshold follows m; smallness/coercivity constants follow ell,a,m,R and precede depth, lattice, alpha, geometry, fields. The cap is 12M alpha. This preserves the frozen headline rather than replacing it by Total or silently uniformising thresholds. |
| Norms/differential | Full Frobenius class norm, trace-normalised SU(2) bond energy, and exterior curl-of-curl `ddA`. The norm factor is handled by existential smallness; no new printed-unit theorem follows. |
| Q/jets/C | Actual frozen componentwise/composite jets, constraints, weights and top-level placement stay. They are not replaced by arbitrary ingredients, but their full printed dictionary is not re-derived here. |
| Eta/tau-star | Retains eta times the pairing of tau-star B with the inverse Nmat acting on tau-star B, plus frozen mass/nonlinear terms. The extra displayed eta/tau-star issue S-3 remains independent and unresolved. |
| Inverses | Frozen totalised inverse and singular constraint fallback remain, with no new well-definedness guard or conclusion. Equality proved here includes those conventions, not a proof that every printed inverse exists. |
| Lambda/support | Touching `OnLambdaT`, touching coarse rows, frozen dropped-bond/axial conditions, block-union Lambda, common R collar, and allowed empty Lambda. These are retained frozen choices, not fresh identification of all printed support conditions. |
| Shell fallback only | `ReadBond` includes edges whose endpoints both miss the cube, so its regularity is stronger than the printed bond convention; its coverage stays frozen. It is copied unchanged but not proved, and is not conflated with the collapsing primary class. |
| Proof-local room condition | No extra 17 ell <= RM or R>=18 premise appears in either proved goal. All frozen theorem thresholds are reused at their original quantifier positions. |

## Final compilation and audit

Only `Attempt.lean` was compiled, serially, using the prescribed command:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s1-touching/r1-prove/Attempt.lean > ../AHP/round2/s1-touching/r1-prove/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/s1-touching/r1-prove/Attempt.lean.exit
```

Final exit: **0**. Final errors/warnings: **0/0**. The final log has 84 lines:
12 type checks and **72 dependency records**, all subsets of
`propext`, `Classical.choice`, `Quot.sound`. All **67 local declarations**
(26 definitions and 41 theorems) have dependency prints; the five directly
used frozen theorem helpers also have prints. The closed goal types are shown
at log lines 33–34. Main dependency records:

```text
'Round2.S1.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round2.S1.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A post-compilation audit checked:

- All **22/22 pinned definition blocks are byte-identical** to `Statement.lean`.
- Every **67/67 local declaration** has a corresponding dependency record.
- All **72/72 records** contain permitted dependencies only.
- Whole-source forbidden-token scan: **0 hits**.
- All imports resolve to frozen modules under `lean/src`; no AHP imports.
- The theorem headers are exactly `goalPos1_proved : GoalPos1` and
  `goalPos2_proved : GoalPos2`, with no surrounding unbound hypotheses.

SHA-256:

- `Attempt.lean`: `d45e27d564812a3b7679b3efdaad008ba833a74604dac5dc66cf32fd78bc5d40`
- `Attempt.lean.log`: `153aef38bce2a0d463ab46fd1907e808a32d11075111d53410026def37385b40`

Only this `r1-prove/` directory was written. No protected file, pin, other AHP
path, Lake configuration, or expected-output file was edited. No build,
reproduction, update, deletion, commit, or push was run. Independent verifier
review is still separate from this builder's checks.
