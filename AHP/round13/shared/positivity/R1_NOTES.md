# Positivity R1 — exact mass absorption, eight physical leaves, localized positivity

## Verdict

**P2 remains OPEN; GoalNeg2 is not proved.** This round proves 32 new supporting declarations, including the actual eight-leaf geometry/mass extraction and unconditional localized right-star positivity. The all-plaquette estimate still requires the complete omitted-plaquette decomposition on central-charged-zero fields. None of the conditional absorption results is advertised as P2.

All six final local/publication compiles exit 0, with only `propext`, `Classical.choice`, `Quot.sound`. `AUDIT.json` checks every printed record, forbidden tokens, exact copies, source/log hashes, and byte identity of the published files. These are builder plus publication executions, **not independent reviewer verification** (blueprint category B).

| Local source | Self-contained shared source | Lines | Printed records | New records |
|---|---|---:|---:|---:|
| `MassAbsorption.lean` | `AHP/round13/shared/positivity/R1_MassAbsorption.lean` | 1058 | 70 | 20 |
| `EightLeaves.lean` | `AHP/round13/shared/positivity/R1_EightLeaves.lean` | 914 | 43 | 9 |
| `LocalPositive.lean` | `AHP/round13/shared/positivity/R1_LocalPositive.lean` | 1472 | 21 | 3 |

Each source has `.lean.log` and `.lean.exit`. The shared files are source certificates, not `.olean` imports. All import only frozen `DrEquiv`. Historical operative definitions are copied verbatim; `COPIES.json` gives source spans and hashes. LocalPositive additionally copies the freshly compiled detection-track `R1_FlatUnit.lean:1-1096`, including the historical full flat-kernel positivity proof, rather than assuming a localized unit. One unused namespace-opening line is omitted from a copied header; no operative declaration is changed.

## 1. The correct comparison is mass-relative, not an ordinary-norm subtraction

The literal statement that the bare star perturbation is negative *only* through the central charged coordinate is false even for the established local atom:

\[
\operatorname{tripleForm}(0,1;0,1,-i)=-2.
\]

`zero_central_arm_negative` proves this exact identity. `halfpi_no_strict_mass_fraction` proves that no coefficient strictly below one pays every half-pi pair using only its two leaf masses. These facts do **not** refute physical P2; the rest of the physical energy is still present. They rule out an unjustified simplification of the proposed proof.

The useful estimate, already implicit in round 12's square completion, is instead

\[
F_{\mathrm{arm}}\ge -(1-\cos t)\,(\|y\|^2+\|z\|^2),
\]

where the full leaf norms include neutral coordinates, and the central neutral square is retained. Sum this over the four arms, paying the eight distinct leaf masses once. Since those masses are a subset of the actual localized mass and the localized delta/gauge terms are nonnegative,

\[
\langle x,A_t x\rangle\ge \cos t\,\langle x,B_t x\rangle.
\]

Thus strict localized positivity suffices for every `0 ≤ t < pi/2`. There is **no additional strictly positive remainder hypothesis** and no need to subtract a guessed norm-loss constant from the existential constant mined in `MINE.md`. On any closed prefix `0 ≤ t ≤ T < pi/2`, the scale/radius-independent relative loss is at most `1-cos T < 1` (`cos_prefix_loss`). We do not claim a positive angle-uniform bound at the endpoint `pi/2`, nor a new uniform ordinary-norm spectral gap. P2's exact open-interval premise is sufficient for FirstCrossing.

### New physical comparison infrastructure

Namespace `AdalyFormal.Round13.Positivity`, source/log lines:

| Declaration | Source line | Axiom-log line | Scope |
|---|---:|---:|---|
| `delta_form_sum_set` | 693 | 65 | Exact frozen plaquette sum for any selector |
| `carrier_form_split` | 736 | 67 | Actual all carrier = actual localized carrier + complete omitted sum |
| `localized_Dpi_nonneg` | 758 | 68 | Full localized delta nonnegative under flat local holonomy |
| `carrier_ge_scaled_local` | 774 | 69 | Mass-relative absorption, conditional on the actual omitted loss |
| `carrier_ge_scaled_local_leaves` | 790 | 70 | Uses genuine distinct level-zero mass rows |
| `full_pair_loss_bound` | 818 | 76 | Full neutral/charged arm lower bound |
| `full_star_loss_bound` | 827 | 77 | Sum over arbitrary arm count without a cardinality loss |
| `cos_prefix_loss` | 849 | 81 | Explicit loss below one on every strict half-pi prefix |
| `zero_central_arm_negative` | 860 | 82 | Bare central-zero arm need not be nonnegative |
| `halfpi_no_strict_mass_fraction` | 865 | 83 | Sharp obstruction to a strict local mass fraction at half pi |
| `plaqEnergy_congr_field` | 907 | 86 | Complete frozen summand depends only on its four input edges |
| `omittedEnergy_eq_raw` | 934 | 87 | Actual complete omitted sum uses RAW input, no inverse-unit premise |
| `localized_positive_of_unit` | 950 | 88 | Flat-local holonomy + actual localized unit gives strict positivity |
| `physical_positive_of_leaf_loss` | 973 | 89 | Conditional full-carrier positivity; physical loss still a premise |
| `frozen_right_zero_first_lower` | 989 | 92 | Actual right atom form, central charged entry in atom 1 |
| `frozen_right_zero_third_lower` | 1004 | 95 | Actual right atom form, central charged entry in atom 3 |
| `omitted_loss_of_injective_arms` | 1021 | 98 | Complete non-star remainder retained as nonnegative; no double counting |

The three other new declarations are `plaqEnergy_nonneg`, `carrier_positive_of_absorption`, and `omitted_loss_of_arm_decomposition`; all details are in `AUDIT.json`. The physical carrier here uses frozen `D1Literal.dataS`; this is definitionally the pinned copy, not a replacement operator.

## 2. Eight DISTINCT actual leaves — now proved

Namespace `AdalyFormal.Round13.Positivity.Leaves` defines `leaf hq R : Fin 8 → Bond ...` at the actual `rightSite hq R`. In order:

1. positive direction-1 normal neighbor;
2. negative direction-1 normal neighbor;
3. positive direction-2 normal neighbor;
4. negative direction-2 normal neighbor;
5. direction-1 tangent at rightSite;
6. direction-1 tangent at its negative direction-1 neighbor;
7. direction-2 tangent at rightSite;
8. direction-2 tangent at its negative direction-2 neighbor.

The fine transverse circumference is **8q**, not 4q. Exact codes `(direction, transverse-coordinate-1, transverse-coordinate-2)` prove all eight are distinct at every q>0. No finite-size numerical assumption is used.

- `leaf_code`: source 816 / log 41.
- `leaf_injective`: 829 / 42.
- `leaf_zero_coord`, `leaf_end_zero_coord`: 839,844 / 43,44.
- `leaf_collar`: 853 / 45, both endpoints outside Omega1 for R≥1.
- `leaf_touching`: 866 / 46, every leaf is an actual touching carrier bond.
- `leaf_level_zero`: 874 / 47, actual level-zero rows for even R≥1.
- `leafSet_card`: 883 / 48, exact cardinality eight.
- `eight_leaf_mass`: 890 / 49, **unconditional physical estimate** for arbitrary U and arbitrary full fine input A:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
  (U : Cfg (scaleUp 2 1 (dilLu q R)))
  (A : BondFnL2 (scaleUp 2 1 (dilLu q R))),
  (∑ i : Fin 8, ‖A (leaf hq R i)‖^2) ≤
    ⟪A, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) A⟫
```

This closes round 12's eight-leaf distinctness/collar/mass-extraction gap, **not** the remaining identification of those leaves with every contribution to the physical star sum.

## 3. Actual localized right-star positivity — now proved

Namespace `AdalyFormal.Round13.Positivity.Local`:

- `rightStar_local_data_flat`, source 1423 / log 19: **all localized data**, at every real angle and any mass a, are exactly their flat-background values. Uses frozen `StatementLaneR8.data_congr`, actual slab admissibility/room, and `starPath_interior`.
- `rightStar_local_positive`, 1443 / 22: for q>0, even R≥18, every real angle, and every nonzero full carrier vector, the **localized** carrier at mass one is strictly positive. It invokes the copied, recompiled `AnalyticR2.dil_flat_pos`; no positivity/unit hypothesis remains.
- `cofinal_rightStar_local_positive`, 1451 / 25: the corresponding nested cofinal dyadic/even-radius statement, with `j=j₀` and `R=2*(R₀+18)`.

These do not assert all-plaquette positivity. They supply the localized positive form needed by the absorption theorem.

## 4. Exact missing statement: P2 (verbatim)

Use the original shared-package openings, including `RightFamily.rightStar`, `IVTR2.rightSite`, original `Qualitative.vacA`, and `AnalyticR1.TwistSpace`:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
```

**No theorem of this type was produced.** No cofinal P2 theorem was produced either. The unconditional all-q/all-even-R supporting geometry above does not interchange the target quantifiers.

### Concrete remaining finite/geometric leaf

With the `Positivity` and `Positivity.Leaves` namespaces open, the substantive missing estimate is the following actual raw omitted-plaquette inequality (the central charged coordinate is written as its literal matrix entry):

```lean
open Classical
open scoped RealInnerProductSpace
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    (((iE (geomOf 2 1 (dilTower q R)) x) (rightSite hq R, (0 : Fin 3)) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0 →
    -(1-Real.cos t) *
      (∑ i : Fin 8, ‖(iE (geomOf 2 1 (dilTower q R)) x) (leaf hq R i)‖^2) ≤
      ∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then 0 else
        plaqEnergy (rightStar hq R t) (iE (geomOf 2 1 (dilTower q R)) x) p
```

To prove it without assuming the target:

1. Use the four actual `P1 rightSite ν` / `P2 rightSite ν` plaquettes. Their injectivity/disjointness are already frozen (`P1_inj`, `P2_inj`, `P1_ne_P2`).
2. On P1, frozen atom 3 is central; on P2, atom 1 is central. Apply the two new actual right-atom lower bounds, keeping its neutral value arbitrary. Match the other atoms' full norms to exactly the eight leaves above.
3. Prove that **every other omitted plaquette contributes nonnegatively** for the full supported field. Some exterior plaquettes have curved holonomy but all input edges vanish: do not claim all non-star plaquettes are globally flat. `plaqEnergy_nonneg` handles flat plaquettes; `curl_bil_zero` handles fully exterior input-zero plaquettes.
4. Apply `omitted_loss_of_injective_arms`, `eight_leaf_mass`, and `carrier_ge_scaled_local`. The localized positive input is now unconditional by `rightStar_local_positive`; `vacA_rightStar` identifies the final all-plaquette operator with the pinned operator.

The compact final join of these published files (deduplicating copied namespaces) also remains to be compiled. Neither a definition of the missing estimate nor a conditional theorem has been passed off as its proof.

## 5. Verification and scope

```sh
python3 AHP/round13/positivity/r1/build.py
bb heavy run -- AHP/round3/lean1.sh AHP/round13/positivity/r1/MassAbsorption.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/positivity/r1/EightLeaves.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/positivity/r1/LocalPositive.lean
# Shared copies were each compiled separately with the same wrapper.
python3 AHP/round13/positivity/r1/audit.py
```

All final six exits are 0; all final logs are free of warnings/errors and nonstandard dependencies. Early development failures were corrected before publication. The 32 new printed declarations, inherited dependency records, and every verbatim-copy check pass. No new numerics, giant join, direct Lean invocation, lake build, reproduction script, commit, push, or deletion was run. Writes by this track are confined to `AHP/round13/positivity/r1/` and `AHP/round13/shared/positivity/` (apart from the authorized lean1 wrapper's shared lock files).
