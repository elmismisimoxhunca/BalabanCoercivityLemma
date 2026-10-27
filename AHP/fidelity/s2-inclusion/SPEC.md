# s2-inclusion — frozen class contains the touching classes

Prediction: **holds**.

This is the source-reviewed inclusion Sol adopted for S-2
(`AHP/attempts/s2-class-implication/SOL_VERDICT.md`): the frozen class contains
the touching classes, so the frozen headline implies the touching-class
headlines. The conclusion stays frozen `InstIneq`. Nothing here is a theorem.
The file was not compiled. Numerical counts are evidence for the product-box
step only.

Sol did not allow: a converse, a strict inclusion, proper-domain non-vacuity,
equality of touching operators with `plaqIn` operators, a resolution of S-1,
or a paper sentence.

## What was repaired

The old draft is `AHP/attempts/s2-class-implication/ClassImplication.lean`.
The repaired text is
[ClassInclusion.lean](/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean),
namespace `AdalyFormal.AHP.FidelS2Inclusion`.

- **F-1.** S-1’s `ClassCoupledTouch` is the corner class. S-2’s draft used that
  name for the weaker four-bond class. This file does not declare
  `ClassCoupledTouch`. `ClassCoupledCorner` is S-1’s conjunction.
  `ClassCoupledFour` is the old four-bond class.
- **F-2.** `TouchBond` is unfolded before the endpoint disjunction is used.
  `CubeBond` is unfolded and the two endpoint goals are rewritten separately
  (the compiled pattern at `ZR8Class.lean:114–119`). The cube equality
  `sites = siteBox` is transported by `▸`, not by `rcases … rfl` under `hc`.
  Headlines are unpacked by `unfold` and nested `rcases`.
- **F-3.** No non-vacuity, no converse, no strictness. Corner saturation is not
  re-proved.

`TouchBond`, `plaqCorner`, `CoversPlaqCorner` and `PerCubeRegularTouch` are the
same text as `AHP/attempts/s1-touching/Touching.lean`. That is as far as the
classes can match. The parallel s1 design was asked to drop corner coverage,
because that clause forces `Ω₀` empty or the whole torus on the paper argument
Sol rejected. A shell whose cubes leave `Ω₀` is not a frozen `IsClassCube`
(`DescribedAt` keeps sites in two strata inside `Ω₀`). No inclusion is stated
for a shell class.

## Variant statement

Frozen anchors, not redefined:
`CubeBond` (`ZStatementP428.lean:145`), `siteBox` (`:122`), `DescribedAt`
(`:131`), `IsClassCube` (`:140`), `CoversPlaqOm0c` (`ZR6A.lean:27`),
`CoversOm0c` (`ZR2A.lean:107`), `ClassCoupled` (`ZR6A.lean:124`),
`PerCubeRegular2` and `CurlReads` (`ZR2A.lean:47`, `:35`), `plaqIn`
(`ZR2Ops2.lean:74`), `InstIneq` (`ZT5A.lean:56`), `CoercG8At` (`:89`),
`P428Core8At` (`:170`), `SidePow6` (`:200`), `P428Genuine8` (`:229`),
`P428Target8` (`:291`).

```lean
def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

def CoversPlaqFour (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p, (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (S.Om 0) e) →
    ∃ sites j, IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

def CoversPlaqCorner (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p, p ∈ plaqCorner (S.Om 0) →
    ∃ sites j, IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

def ClassCoupledFour (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqFour ell M c k S ∧
    PerCubeRegularTouch ell M c k S α₀ η U

def ClassCoupledCorner (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧
    PerCubeRegularTouch ell M c k S α₀ η U

def P428Target8Four : Prop :=
  ∀ ell ≥ 2, ∀ a > 0, ∃ m₀ ≥ 1, ∀ m ≥ m₀, ∃ R₀, ∀ R ≥ R₀,
    SidePow6 ell (ell ^ m) a ∧
    ∃ a₀ > 0, ∃ γ₀ > 0, ∀ k ≥ 1, ∀ Lu, ∀ α₀ > 0,
      (12 : ℝ) * (ell ^ m) * α₀ ≤ a₀ →
        CoercG8AtFour ell (ell ^ m) R k _ a Lu 12 α₀ γ₀
-- CoercG8AtFour is CoercG8At with ClassCoupled replaced by ClassCoupledFour.
-- Conclusion is InstIneq, still summed on plaqIn.
```

`P428Target8Corner` is the same with `ClassCoupledCorner`. `PerCubeRegularTouch`
is `PerCubeRegular2` with every `CubeBond` / `CurlReads` hypothesis widened to
`TouchBond` / `CurlReadsTouch`. The `∃ g, A` stays inside `∀` cube. Factor `12`
and the smallness bound are unchanged. `Λ` stays the frozen touching reading.

Drafted implications, uncompiled:

```lean
theorem ClassCoupledCorner.toFour :
    ClassCoupledCorner ell M c k S α₀ η U → ClassCoupledFour ell M c k S α₀ η U

theorem ClassCoupledFour.toFrozen :
    ClassCoupledFour ell M c k S α₀ η U → ClassCoupled ell M c k S α₀ η U

theorem ClassCoupledCorner.toFrozen :
    ClassCoupledCorner … → ClassCoupled …

theorem targetFour_of_frozen : P428Target8 → P428Target8Four
theorem targetCorner_of_four : P428Target8Four → P428Target8Corner
theorem targetCorner_of_frozen : P428Target8 → P428Target8Corner
```

Why the direction is the frozen class containing the touching class:

- `CoversOm0c` does not mention `CubeBond`, so it is shared.
- A `plaqIn` plaquette is a four-touch plaquette (`CubeBond → TouchBond`).
  The witness `IsClassCube` is a `siteBox`. Touch-covering a unit square by a
  product box puts all four corners in the box, hence `CubeBond`. That is
  `CoversPlaqFour.toFrozen`. Bond-predicate monotonicity alone does not give it.
- One-corner coverage has a larger antecedent than four-touch coverage, so
  `CoversPlaqCorner → CoversPlaqFour`. The one-corner clause is added; it is
  not the printed bond convention by itself.
- `PerCubeRegularTouch → PerCubeRegular2` restricts the bounds from touching
  bonds to both-endpoint bonds. No geometry.
- The headlines only repackage `∃ m₀, R₀, a₀, γ₀`. Thresholds stay after
  `ell` and `a`. `a₀` and `γ₀` stay before `k`, the torus and `α₀`. No new
  uniformity in `m` or `R`.

## Numerical method and results

Script:
[inclusion_geometry.py](/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s2-inclusion/numerics/inclusion_geometry.py).
Output:
[results.json](/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s2-inclusion/numerics/results.json).
Runtime 0.782 s, side at most 8, far under 4 GB. Numpy only. No gauge-field
operator is modelled, because the claim does not change `Δ` or `J`.

Predicates transcribed: `periodicLatticeShift` (`ClayStatement.lean:1281`),
`periodicPlaquetteBoundaryEdges` (`:1295`), `siteBox` (`ZStatementP428.lean:122`),
`CubeBond` (`:145`), `plaqIn` (`ZR2Ops2.lean:74`), and the touching/corner
formulas in `ClassInclusion.lean`. `IsClassCube` is not decided: the script
never checks `GridCorner`, the stratum clause, or `Admissible`.

**Product-box step.** For every `siteBox` (every corner, every side `0…N`) and
every unit plaquette on the 3-torus of side `N ∈ {2,4,6,8}`: if all four
boundary bonds are `TouchBond` of the box, all four corners lie in the box, so
the bonds are `CubeBond`. The converse (a `CubeBond` cover is a `TouchBond`
cover) was counted on the same set.

| N | plaquettes | boxes | touch-covers | touch without cube | cube without touch |
|---|------------|-------|--------------|--------------------|--------------------|
| 2 | 24 | 24 | 192 | 0 | 0 |
| 4 | 192 | 320 | 14,976 | 0 | 0 |
| 6 | 648 | 1,512 | 224,208 | 0 | 0 |
| 8 | 1,536 | 4,608 | 1,603,584 | 0 | 0 |

Zero failures, including boxes that wrap. This is evidence for
`touchCover_cubeBond`, not a proof. `shift_comm` (`ZR8Class.lean:87`) was
checked on every plaquette: the two ways of building corner `D` agreed.

**Two set-level domains on the side-8 torus.** Not admissible towers, and not
class cubes.

- Product block `siteBox(0, 4)`, 64 sites, proper and nonempty. `plaqIn` = four-touch
  = 108 (the hand count `(3·3·4)·3`). `plaqCorner` = 300, so 192 one-corner
  plaquettes are not four-touch. Exit plaquette corners
  `(3,0,0), (4,0,0), (3,1,0), (4,1,0)`: two corners in, bond `BD` with both
  endpoints out, so it is `plaqCorner` and not four-touch and not `plaqIn`.
  Of 100 `siteBox`es contained in the block, none touch-covers that plaquette.
- L of two side-2 blocks, `[0,2)³` and `[2,4)×[2,4)×[0,2)`, 16 sites.
  `plaqIn` = 12, four-touch = 14, `plaqCorner` = 106. The two extra four-touch
  plaquettes are the diagonal squares at `z = 0` and `z = 1`. Focus corners
  `(1,1,0), (2,1,0), (1,2,0), (2,2,0)`: opposite corners in, four-touch, not
  `plaqIn`. Of 18 `siteBox`es contained in the L, none touch-covers it.
  Set-level four-touch coverage therefore fails on this union, for the same
  geometric reason: a witness box inside the set cannot contain the outside
  corners. The inclusion `CoversPlaqFour → CoversPlaqOm0c` is then vacuous on
  that set. That is consistent with the drafted implication and is not a
  non-vacuity witness.

**Bond count on the side-4 product box** (`PerCubeRegular2` at `ZR2A.lean:47`
uses `CubeBond` only as a hypothesis). Edges are `PeriodicLatticeEdge`: 144
`CubeBond`, 240 `TouchBond`, 96 extra. Touching regularity quantifies more
bonds on this one box, which is why `PerCubeRegularTouch.toFrozen` is a
restriction. It is not a strict-inclusion witness for the classes: no `U` and
no `Admissible` tower were built.

These counts do not show that `ClassCoupledFour` is inhabited, that
`ClassCoupledCorner` is empty on every proper domain, or that either class is
strictly smaller than `ClassCoupled`.

## Stage B Lean plan

Do not edit `lean/lakefile.toml`. After `REPRODUCE.sh` has produced oleans,
from `lean/`:

```text
lake env lean ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean
```

Direct imports, already at the top of that file:

1. `ZT5A` — `P428Target8`, `P428Genuine8`, `P428Core8`, `P428Core8At`,
   `SidePow6`, `CoercG8At`, `InstIneq`, and through `ZR6A` / `ZR2A` the frozen
   class (`ClassCoupled`, `CoversPlaqOm0c`, `CoversOm0c`, `PerCubeRegular2`,
   `CurlReads`, `IsClassCube`, `CubeBond`, `siteBox`).
2. `ZR2Ops2` — `plaqIn`.
3. `ZR8Class` — `shift_ne` (`:52`), `shift_comm` (`:87`).

No import of `AHP/attempts/s1-touching/Touching.lean` or of the old
`ClassImplication.lean`. Those namespaces must stay separate.

If boundary `simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert,
Finset.mem_singleton]` fails on the `by classical` body (`ClayStatement.lean:1295`),
the fallback already used in the tree is `unfold periodicPlaquetteBoundaryEdges`
then the same `simp only` (`AC_GE4.lean:90`, `ZR8Class.lean:119`). Do not change
the statement to make a tactic succeed.

Then `#print axioms` on at least:

- `AdalyFormal.AHP.FidelS2Inclusion.touchCover_cubeBond`
- `AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqFour.toFrozen`
- `AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqCorner.toFour`
- `AdalyFormal.AHP.FidelS2Inclusion.PerCubeRegularTouch.toFrozen`
- `AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledFour.toFrozen`
- `AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFour`
- `AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFrozen`
- `AdalyFormal.AHP.FidelS2Inclusion.targetFour_of_frozen`
- `AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_four`
- `AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_frozen`

Accept only a subset of `propext`, `Classical.choice`, `Quot.sound`.
`Classical.em` in `opposite_of_touch` should account for `Classical.choice`.
Anything else, or a failure to elaborate, leaves S-2 unclosed. A successful
print still does not give non-vacuity, a converse, operator agreement, or a
paper sentence.
