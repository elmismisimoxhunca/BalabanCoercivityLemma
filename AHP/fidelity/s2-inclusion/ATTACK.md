# ATTACK — s2-inclusion (Kimi)

Scope: `SPEC.md`, `lean/ClassInclusion.lean`, `numerics/inclusion_geometry.py`,
`numerics/results.json`, checked against `lean/src` (frozen), `HANDOFF.md`,
`paper/OPEN_ITEMS.md` (B, K–N, R, S), `notes/statement_sheet.tex`, and the two
prior attempts `AHP/attempts/s1-touching/`, `AHP/attempts/s2-class-implication/`.
No `lean`/`lake`/`REPRODUCE.sh` was run. Nothing outside `AHP/fidelity/s2-inclusion/`
was written (`git status --porcelain` shows only untracked `.bb/`, `AHP/`).

**Bottom line: the attack does not break the design.** The inclusion direction
is the right one, every cited frozen line is exact, the numerics reproduce
bit-for-bit and use no tolerances to be dishonest with, and my independent
extension of the numerics (odd and degenerate tori, exhaustive corner-saturation
scan) confirms rather than refutes the design's geometry. What survives is a
list of disclosure sharpenings and compile-time risks, below.

## 1. Does the variant say what it claims?

Yes, with one wording slip (F1).

- **Direction.** S-2 asks: the frozen class contains the touching class, so the
  frozen theorem implies the touching-class version. The draft proves (as text)
  `ClassCoupledCorner → ClassCoupledFour → ClassCoupled` and
  `P428Target8 → P428Target8Four → P428Target8Corner`. Membership-wise this is
  exactly "touching-class configurations ⊆ frozen-class configurations", and the
  headline implications are the correct contravariant consequence. No converse
  or strictness is claimed. ✓
- **Quantifier order.** `P428Target8Four/Corner` copy `P428Target8`
  (`ZT5A.lean:291`) binder by binder; `P428Core8AtFour/Corner` copy
  `P428Core8At` (`:170`); `P428Core8 = P428Core8At … 12` is `rfl`-pinned at
  `:176`, so the draft's `unfold P428Core8; unfold P428Core8At` chain has a real
  target. Smallness `(12:ℝ)*M*α₀ ≤ a₀` unchanged; factor 12 unchanged. ✓
- **Conclusion.** `InstIneq` (`ZT5A.lean:56`) with `Δ`, `J` on `plaqIn`
  (`ZR2Ops2.lean:74`) is untouched; `Λ` predicates untouched. The variant does
  not claim an operator-side (S-1) result, matching sheet rows 5 and 7. ✓
- **The class swap is exactly what is claimed.** `CoversPlaqFour` is
  `CoversPlaqOm0c` (`ZR6A.lean:27`) with both `CubeBond` occurrences replaced by
  `TouchBond`; `PerCubeRegularTouch` is `PerCubeRegular2` (`ZR2A.lean:47`) with
  `CubeBond → TouchBond` and `CurlReads → CurlReadsTouch` (`ZR2A.lean:35`),
  bounds and quantifier nesting identical (`∃ g,A` inside `∀` cube).
  `ClassCoupled` is `CoversOm0p ∧ PerCubeRegular2` (`ZR6A.lean:124`) with
  `CoversOm0p = CoversOm0c ∧ CoversPlaqOm0c` (`:33`), so
  `ClassCoupledFour.toFrozen`'s constructor shape `⟨⟨h.1, …⟩, …⟩` matches. ✓
- **The S-1 conjuncts claim is accurate.** s1's `ClassCoupledTouch`
  (`Touching.lean:370`) is literally `CoversOm0c ∧ CoversPlaqCorner ∧
  PerCubeRegularTouch` — the same conjuncts the draft gives `ClassCoupledCorner`
  under a non-colliding name, and the shared def texts (`TouchBond`,
  `plaqCorner`, `CoversPlaqCorner`, `CurlReadsTouch`, `PerCubeRegularTouch`)
  match s1's. F-1 of the repair is real: s1's name meant the corner class, the
  old s2 draft used it for the four-bond class. ✓
- **F1 (minor, wording).** SPEC says the s1 design dropped corner coverage
  "because that clause forces Ω₀ empty or the whole torus on the paper argument
  Sol rejected". Misattribution: Sol's s1 verdict **upheld** the saturation
  argument as coherent ("F5 is essential, not optional wording… a
  necessary-condition argument"); what Sol rejected was the s1 draft **as a
  resolution of S-1** (broken script + vacuity consequence). The saturation
  itself is drafted but uncompiled (`saturated_of_coversCorner`,
  `Touching.lean:686`) and the s2 file correctly does not re-prove it (F-3).
  Recommend the SPEC sentence be reworded so a reader does not think the
  saturation argument was found wrong.

## 2. Citation audit (all exact)

`siteBox` `ZStatementP428.lean:122` ✓; `DescribedAt` :131 ✓; `IsClassCube` :140
✓; `CubeBond` :145 ✓; `bigSide` :51 ✓; `towerBj = Om j \ Om (j+1)` :118 ✓;
`CoversPlaqOm0c` `ZR6A.lean:27` ✓; `CoversOm0p` :33 ✓; `ClassCoupled` :124 ✓;
`CurlReads` `ZR2A.lean:35` ✓; `PerCubeRegular2` :47 ✓; `CoversOm0c` :107 ✓;
`plaqIn` `ZR2Ops2.lean:74` ✓; `InstIneq` `ZT5A.lean:56` ✓; `CoercG8At` :89 ✓;
`P428Core8At` :170 ✓; `SidePow6` :200 ✓; `P428Genuine8` :229 ✓; `P428Target8`
:291 ✓; `periodicLatticeShift` `ClayStatement.lean:1281` ✓;
`periodicPlaquetteBoundaryEdges` :1295 ✓ (edge order `(x,μ), (shift x μ,ν),
(shift x ν,μ), (x,ν)` — exactly the draft's AB, BD, CD, AC); `shift_ne`
`ZR8Class.lean:52` ✓; `shift_comm` :87 ✓; the boundary-simp pattern
`ZR8Class.lean:119` and the `unfold … ; simp` fallback at `AC_GE4.lean:90` ✓.
Namespaces opened by the draft cover every frozen name it uses
(`StatementLane`, `StatementLane2`, `StatementLaneG`, `IngredientFamilyR2`,
`Target.ClayStatement`; `LambdaOK2` is in `StatementLaneG` via `ZT4A`, inside
`ZT5A`'s cone). A `grep` over `lean/src` finds no existing declaration named
`TouchBond`, `plaqCorner`, `CoversPlaqFour/Corner`, `ClassCoupledFour/Corner`,
`PerCubeRegularTouch`, `CurlReadsTouch`, or the `*Four/*Corner` headlines — no
collisions with the opened namespaces.

## 3. Numerical-operator transcription audit

- `periodicLatticeShift` = `Function.update x μ (x μ + 1)` (`Fin` addition wraps
  mod `L μ + 1`) ↔ Python `(B+1) % n` ✓.
- `siteBox`: Lean `((x μ).val + (L μ + 1) − (z μ).val) % (L μ + 1) < s` ↔ Python
  `(points − z) % n < s`; identical residues for `0 ≤ x,z < n` ✓.
- The four Lean boundary edges give TouchBond-mask `(A|B)&(B|D)&(C|D)&(A|C)` and
  CubeBond-mask `A&B&C&D`; Python `classify` implements exactly these ✓.
- `plaqCorner` = one of four corners ✓; `plaqIn` = CubeBond on all four edges =
  all four corners in ✓.
- Box sizes `s > n` collapse to the whole torus (= `s = n` case), `s = 0` is
  empty (antecedent false): the scan range `0…n` is exhaustive over distinct
  boxes ✓.

## 4. Numerical honesty

Re-ran `inclusion_geometry.py`: output matches `results.json` exactly except
timings (MATCH; ~0.8 s, side ≤ 8, numpy only, far under 4 GB). All counts are
exact integers — there are no tolerances to game. Hand cross-checks of the
reported numbers: product block `plaqIn = fourTouch = 108 = (3·3·4)·3` ✓;
contained boxes `100 = 64+27+8+1` ✓; L-shape contained boxes `18 = 16+2` ✓;
side-4 box bonds: CubeBond `144 = 48·3`, TouchBond `240 = 80·3` ✓. The exit
plaquette and diagonal plaquette records in `results.json` are internally
consistent (A,C in / B,D out; fourTouch true, plaqIn false; 0 covering boxes).

**F2 (evidence gap, closed by this attack).** The design scans only even sides
2,4,6,8, while the print's blocking factor is odd `L > 11` (OPEN_ITEMS S-4). The
Lean lemmas are parity-free, but the evidence was not. I ran the identical scan
on sides **1, 3, 5, 7** (`attack_checks.py`, `attack_results.json`, 1.8 s):
`touch_without_cube = 0` and `cube_without_touch = 0` everywhere, including the
degenerate side-1 torus (2-edge boundary finset). The gap is empirically closed;
recommend the SPEC table mention odd sides or absorb this run.

## 5. Hypothesis-class checks (run, set/box level)

**ClassCoupledCorner — numerically vacuous on every proper nonempty Ω₀ tested.**
A class cube is a `siteBox` contained in two strata (`DescribedAt` :131–137),
hence in Ω₀ under `Admissible`; so `CoversPlaqCorner` requires every one-corner
plaquette to be touch-covered by a siteBox ⊆ Ω₀. `attack_checks.py` checks, for
**all 254 proper nonempty subsets** of the side-2 torus (exhaustive) and 462
structured/random subsets of the side-3 torus (all 1-site sets and complements,
all proper product boxes and complements, 300 random masks): every one has a
`plaqCorner` plaquette touch-covered by **no** contained siteBox (5,736 and
21,137 uncoverable plaquettes respectively; zero subsets pass). This is the
mechanism of s1's drafted `saturated_of_coversCorner` (needs `Admissible`,
`2 ≤ M`; uncompiled) confirmed at box level. Consequence the SPEC should state
as sharply as Sol's s1 F-5 does: **if compiled, the corner implication is true
but its antecedent class has no proper-nonempty-Ω₀ member in this geometry; its
content is confined to Ω₀ = ∅ or the whole torus**, where `plaqCorner = plaqIn`.
The SPEC's "no non-vacuity" disclosure covers this only implicitly.

**ClassCoupledFour — proper nonempty Ω₀ not excluded; inhabitation not
decidable here.** On every siteBox domain (sides 2,3,4,5, all boxes),
`fourTouch == plaqIn` (0 mismatches) — on product boxes the four-touch
antecedent collapses to the frozen one, so coverage transfers from frozen
witnesses on box domains. But a real member needs factor-12 grid-aligned class
cubes (side `12·M·ell^j ≥ 24`) inside a proper Ω₀, which no torus of side ≤ 8
admits: **small-torus numerics cannot exhibit or refute inhabitation**; the
route is frozen non-vacuity witnesses with product-box level-0 domains plus
`U = 1` (`A = 0` satisfies every TouchBond bound since `0 < f·M·α₀·(…)`), and
that is a Lean question outside this stage. The design claims no non-vacuity ✓.

## 6. Elaboration risks (Stage B decides; none is a missing mathematical step)

1. `simp only [periodicPlaquetteBoundaryEdges, …]` on the `by classical` body —
   the SPEC already carries the `unfold` fallback (`AC_GE4.lean:90` pattern). ✓
   disclosed.
2. `mem_siteBox_iff` by `rfl` — relies on `∈ setOf` unfolding; plausible, cheap
   to fix (`Iff.rfl`/`intro` iff) if it fails.
3. `cornerA…cornerD` are plain defs used through `let d1/d2`, `▸`-transports and
   `congrArg Fin.val`; every step is defeq-sound on reading, but only
   elaboration settles the `rw`/`▸` motive inference in
   `siteBox_fill_of_*` and `square_edges_touch` (third bullet's
   `cornerD_comm p ▸ hD`).
4. `hsites ▸ hc` in `CoversPlaqFour.toFrozen` must rewrite **both** occurrences
   of `sites` inside `IsClassCube` (including the uniqueness clause) — that is
   the intended simultaneous rewrite; a motive-inference failure would be a
   tactic issue, not a hole (F-2's documented repair).
5. `cubeAnte_iff_plaqIn` (both directions `simpa [plaqIn, CubeBond]`) is unused
   by the inclusion chain — dead weight, harmless.
6. `Classical.em` in `opposite_of_touch` will put `Classical.choice` in the
   axiom print — within the accepted set; the SPEC says so. ✓

## 7. What this attack could not do

No Lean was run (stage rule): elaboration, the `#print axioms` list, and the
`Classical.choice` attribution are unverified. Inhabitation of either touching
class is undecided (Section 5). Odd-side numerics at side ≥ 9 and any
statement about real factor-12 cubes are beyond the side ≤ 8 envelope.

## 8. Recommendation to Sol

The design's mathematics survives attack: correct direction, exact citations,
reproduced numerics, honest scoping. Adopt-with-disclosures material: **F1**
(reword the "Sol rejected" sentence — Sol upheld the saturation argument), **F2**
(odd/degenerate sides now covered by `attack_results.json`; fold in or cite),
and state explicitly that the corner class is numerically saturated to
∅/whole-torus on every proper nonempty domain tested, so the corner headline's
content is confined there; the four-bond class is the variant with potential
proper-domain content, and its inhabitation remains unshown. S-2 stays
uncompiled; nothing here closes it.
