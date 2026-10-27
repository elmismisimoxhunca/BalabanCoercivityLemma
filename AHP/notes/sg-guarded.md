# SG — guarded all-plaquette reading

Uncompiled draft: [PencilPin.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/sg-guarded/PencilPin.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited.

`P428Target8SG` is not proved and not refuted. It is not the printed lemma. `full_guard_literal` is a different statement.

## What the frozen text already says

`P428Target8SG` (`lean/src/D2Cons.lean`) asserts the literal inequality only where `Ginv` is a unit. For the selectors `selAll`, `selAll` that statement is equivalent to `GuardResidualT` (`P428Target8SG_iff_residualT`) and to `GuardPencilT` (`P428Target8SG_iff_pencilT`, `lean/src/DrEquiv.lean`). The equivalence does not keep the same existential thresholds. This draft does not re-prove it.

`GuardPencilT` is the headline quantifier prefix — `ell ≥ 2`, `a > 0`, eventual `m`, `R`, `a₀`, then every `k ≥ 1`, every small `α₀`, `TorusOK`, `Admissible`, `LambdaOK2`, `ClassCoupled` at factor `12`, and one positive-energy test field — with conclusion

\[
\mathrm{IsUnit}\,\mathrm{Ginv}_{\mathrm{lit}} \to \mathrm{IsUnit}\,(\mathrm{Ginv}_{\mathrm{lit}} - \Delta^{(2)}_{\mathrm{loc}}).
\]

The identity behind that conclusion is `G1inv_lit_eq_pencil` (`lean/src/DrRed1.lean`): under admissibility, `0 < ell`, and the collar `17 ell ≤ R M`, if the literal `Ginv` is a unit and the localised data are `WellDefAt selIn selIn`, then `G1inv_lit = Ginv_lit - Delta2_loc`. No unit hypothesis on the literal `G1inv` enters that identity.

`SolR345Audit.full_guard_literal` (`lean/src/SolR345Audit.lean`) proves `P428Target8SG2 selAll selAll`. `P428Target8SG2` (`lean/src/GdGap.lean`) guards by `WellDefAt`, and `WellDefAt` is `IsUnit Ginv ∧ IsUnit G1inv ∧ IsUnit (Q G1 Q*)`. The full guard assumes the pencil is already a unit. It is not the missing direction.

## The pin

Along an exterior-only path the correction is constant and class membership is preserved from the starting configuration. This does not supply an in-class start.

`Zb Ω₀` (`lean/src/D1Path.lean`) is the set of bonds with no endpoint in `Ω₀`. An exterior-only path fixes every bond outside that set. On any such path, under admissibility, `ell ≥ 2`, and the collar `17 ell ≤ R M` (and, for the pencil identity, localised `WellDefAt` at the start):

* `Delta2_loc` does not depend on the path parameter (`Delta2_loc_const`, `lean/src/DrPath2.lean`).
* Localised `WellDefAt` is copied from the start (`WellDefAt_loc_const`).
* `ClassCoupled` at the same `α₀` is copied from the start (`classCoupled_path`). The regularity half only reads `CubeBond (S.Om 0)`, which is `BothIn Ω₀` (`perCubeRegular2_congr`, `lean/src/ZT6B.lean`). Those bonds are disjoint from `Zb`. The headline bound `12 M α₀ ≤ a₀` does not constrain links in `Zb Ω₀`.
* Where `Ginv_lit(t)` is a unit, `G1Lit t = GinvLit t - DeltaLoc0` (`G1Lit_eq`, `lean/src/DrPath3.lean`).
* The literal inverse moves only by the all-plaquette shift (`Ginv_lit_path`, `lean/src/DrPath1.lean`):

\[
\mathrm{Ginv}_{\mathrm{lit}}(t) = \mathrm{Ginv}_{\mathrm{lit}}(0) + p_E W_0^\ast(\Delta_t - \Delta_0) W_0 i_E,
\]

with `Δ` the normalised operator on every plaquette.

So on this family the pencil is a constant shift of a moving literal inverse:

\[
\mathrm{G1inv}_{\mathrm{lit}}(t) = \mathrm{Ginv}_{\mathrm{lit}}(0) + \mathrm{Shift}(t) - D, \qquad D = \Delta^{(2)}_{\mathrm{loc}}(0).
\]

At a fixed configuration satisfying the other premises, failure of the pointwise transfer means `Ginv_lit(0) + Shift` is a unit and `Ginv_lit(0) + Shift - D` is not. A single such configuration does not refute the eventual headline. To refute `GuardPencilT`, one needs fixed `ell ≥ 2` and `a > 0` such that, for every `m₀`, there is `m ≥ max m₀ 1`, for every `R₀` there is `R ≥ R₀`, and for every `a₀ > 0` there is a configuration satisfying all remaining premises (including the smallness bound and a positive-energy test field) with this pointwise failure. One path at one scale only defeats thresholds that include that scale. A cofinal family of separating exterior paths is a sufficient route, not a necessary path representation proved here. The twist path `U_θ` is one exterior-only path. It is not the only one. Showing that the twist path never separates would not prove `GuardPencilT`.

## What this draft records (uncompiled)

Pure Mathlib, in `PencilPin.lean`. Not the lattice operators.

The transfer `IsUnit A → IsUnit (A - D)` is false for `ℝ →L[ℝ] ℝ` (`not_generic_unit_transfer`). The scalar path `carrier t = (2 - t) • 1` with correction `1` is a unit at `t = 1`, and the pencil is not. Both are units for every `t < 1`. The carrier itself is singular only at `t = 2` (`scalar_path_crosses_earlier`). At `t = 0` the pencil form is nonnegative. At `t = 3` it is negative on `1`. A zero correction does not move the root (`unit_of_zero_correction`).

On a finite-dimensional real inner product space the complementary half is general: if `A` is `c`-coercive and `c > ‖D‖`, then `A - D` is a unit. Any failure forces `c ≤ ‖D‖` (`coercivity_le_opNorm_of_pencil_fail`). The same window is already specialised in the tree as `G1inv_lit_isUnit_of_margin` and `coercivity_le_Delta2_of_gap` (`lean/src/DrMargin.lean`). This file does not import those proofs.

The scalar path is not a counterexample to `P428Target8SG`. It has no tower, no class, and no test field.

## Where a decision has to live

A proof of the missing direction has to use something the scalar path does not have. Coercivity of literal `Ginv` with room above `‖Delta2_loc‖` would do it, by the margin. `IsUnit` alone does not. The full guard does not. `SepPathFamily2` (`lean/src/DrFamily2.lean:36`) has the cofinal scale and smallness quantifiers needed for a refutation, together with sufficient path hypotheses: an in-class continuous exterior path, `Ginv_lit` a unit on a compact interval, the pencil positive semidefinite at the left endpoint, a negative direction at the right. The source supplies `not_GuardResidualT_of_sep2` and `not_P428Target8SG_of_sep2`; it does not supply the converse from headline failure to such paths. Thus this is a sufficient certificate, not an established equivalence with the negation. The bracket that turns those sign hypotheses into a non-unit is already `exists_nonunit_path` (`lean/src/D1IVT.lean:86`) and `pencil_bracket_unit` (`lean/src/DrBracket2.lean:20`). `SepPathFamily2` is not proved. Its skeleton is not a gated module.

Known points that do not decide it:

* Near the flat twist, on the depth-two slab `ell = 2`, `k = 2`, `a = 1`, both literal units hold on some existential interval (`nv_guard_nonvacuous`, `lean/src/GdR5b.lean`). The radius is not uniform, and the statement is not every exterior value.
* At angle `π` on that slab, `domination_fails_pi` (`lean/src/GdR6a.lean:109`) gives a vector on which literal `Ginv` is negative while localised `Ginv` is nonnegative. Thus their difference is not positive semidefinite. This declaration alone says nothing about a corrected `G1inv` difference. Units at `π` are not proved. A negative direction does not imply singularity. This is not a pencil non-unit.
* If `Delta2 = 0`, the two roots coincide. That happens when the source is orthogonal to the range that `Delta2` sees (`Delta2_eq_zero_of_Jperp`), and on the base-flat family `G1invS = Ginv` (`G1invS_eq_Ginv_base`). Those paths do not separate the pencil from `Ginv`. A separating path needs a nonzero localised correction. The base-flat freeze is bonds whose base point lies in `Ω₀`, not `Zb`.

## Obstruction

This draft supplies no lattice witness and computes no spectrum. Links in `Zb Ω₀` take values in a compact group, so the ambient space of exterior completions on one fixed torus is compact; the headline still quantifies over arbitrarily large `m` and `R`, and the bond space grows. A one-torus matrix does not refute `GuardPencilT`. No uniform smallness estimate for `Shift` is supplied here; `classCoupled_path` preserves membership without imposing linkwise `α₀`-smallness on `Zb`. A source-specific coercivity margin for literal `Ginv` above the fixed correction norm would be a sufficient positive route, but no such margin over the whole class unit domain is established. If noncoercive units occur, a positive argument would have to handle those by a different route. A sufficient negative route is a family of exterior paths obeying the full cofinal scale and smallness quantifiers stated in the pin, on which `Ginv_lit(t) - D` hits a kernel while `Ginv_lit(t)` is still a unit. Neither route is supplied here.

## What this does not say

- Not that `P428Target8SG` is true, and not that it is false.
- Not that `SepPathFamily2` is inhabited.
- Not that the scalar path, the angle `π`, or non-vacuity near `0` decides the guard.
- Not that `full_guard_literal` is the guarded headline.
- Not a theorem of the project tree. No `lean` run, no axiom print. `compiled` is false.
