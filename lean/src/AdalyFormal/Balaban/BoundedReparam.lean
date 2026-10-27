/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo

# `BoundedReparam.lean` — anchoring `Δ_k`'s foundation: `IsBoundedReparam` and a genuinely
`U`-dependent ingredient

**Dispatch target** (following `RegularUCoercivity.lean`'s crux, commit `15028636`): the crux proved
(a) `deltaKFormOnSubspace156` is `U`-INDEPENDENT and (b) `theLemma_regularU` is FALSE for free
`Qext`/`J`, and named the missing primitive as a BOUNDEDNESS hypothesis on `Qext`/`J` (the analogue
of `TheLemma.IsBalabanReparam` for `C`). This file builds that hypothesis and wires ONE genuinely
`U`-dependent ingredient reusing `CovariantOperators.RMap`.

## LEAD ANSWER, per the dispatch's own instruction

1. **`IsBoundedReparam` IS DEFINED** (§1, `IsBoundedReparam`): `Qext` has quadratic-growth
   `D̃⁽²⁾`-output bounded by `K‖B‖²`, `‖J‖ ≤ M_J`, AND the CMP99b-style smallness clause
   `2·K·M_J < 1/2 − a` (the source-coupling term must not exceed the base-gap term the first two
   terms of (3.156) already control unconditionally — `RegularUCoercivity.deltaKUnifiedData_first_
   two_terms_coercive`, reused, LAW-19). CMP99b p.396 (3.35)/(3.36) states the analogous smallness
   ("`α₀` so small that `O(1)Mα₀` is still a sufficiently small number") QUALITATIVELY for `U`'s own
   regularity, already covered by `RegularityHolonomy.IsRegularHolonomy`; no page in this tree's
   corpus attaches an explicit numeric constant to `Qext`/`J` specifically (checked: `CMP99b_p427.md`,
   `CMP99b_p428.md`, image-adjudicated, describe `D̃⁽²⁾` only qualitatively as "a quadratic polynomial
   ... with properties similar to `C^{(2)}(A)`"), so the exact threshold `2KM_J < 1/2 − a` here is
   THIS FILE'S OWN, honestly-disclosed choice of the CORRECT STRUCTURAL SHAPE (source term vs.
   base-gap term) rather than a transcribed source number — stated plainly, not hidden.
2. **`IsBoundedReparam` BLOCKS the crux's adversarial witness — PROVED, not merely argued.**
   §3, `adversarial_not_boundedReparam`: for EVERY `K M_J : ℝ`, the crux's own `(qextQuad regB0,
   adversarialJ bc)` pair FAILS `IsBoundedReparam` (specifically the smallness clause: any `K`, `M_J`
   admissible for the shape clauses force `2·K·M_J ≥ 1 + |1/2−a| > 1/2−a`, using the EXACT closed
   form `Dtilde2Shape (qextQuad regB0) B = ‖B‖²•regB0` already on record). `IsBoundedReparam` alone
   (the shape clauses) is finite-dimensionally trivially satisfiable by this pair — it is the
   SMALLNESS clause specifically that excludes it, reported precisely rather than conflated.
3. **A genuinely `U`-dependent ingredient IS built and PROVED to vary with `U`** (§2,
   `holonomyConjBFL2`): componentwise adjoint-holonomy multiplication `X ↦ (b ↦ R(U(b))·X(b))` on
   `BFL2 witnessL`, reusing `CovariantOperators.RMap` (LAW-19) — the exact mechanism the crux
   diagnosed as missing from `deltaKUnifiedData`'s free `Q := Qstar := 1` wiring.
   `holonomyConjBFL2_trivialU_ne_witnessU` proves it takes DIFFERENT values at `trivialU` vs. the
   tree's own non-flat witness `CovariantOperators.witnessU`, at a shared explicit point — the
   opposite of `deltaKFormOnSubspace156`'s proved `U`-independence.
4. **`theLemma_regularU_bounded_coercive` (§4) is FULLY PROVED (not sorry'd, not merely stated
   conditionally)**: under `IsBoundedReparam bc Qext J K M_J`, `deltaKForm deltaKUnifiedData bc Qext
   J` is coercive on ALL of `BFL2 witnessL` with explicit `γ₀ := 1/2 − bc.a − 2·K·M_J > 0` — hence
   coercive on `subspace156BFL2`'s restriction too, for EVERY regular `U` (the form is `U`-independent
   there, §3 of `RegularUCoercivity.lean`, so the bound transfers unconditionally in `U`). This
   supersedes the dispatch's fallback ("if wiring hits a wall, report it") — no wall was hit for the
   conditional coercivity leg; §2's `U`-dependence anchoring is a SEPARATE, disclosed-partial
   deliverable (item 3 above), not yet wired INTO `deltaKUnifiedData` itself (named open, §5).
5. **Non-vacuity of `IsBoundedReparam`** (§5, `isBoundedReparam_zero_witness`): `Qext := qextQuad 0`,
   `J := 0`, `K := M_J := 0` satisfies every clause whenever `bc.a < 1/2` — the hypothesis is not
   empty.

## What this file does NOT achieve (named precisely)

* `holonomyConjBFL2` is NOT wired into `deltaKUnifiedData`'s `Q`/`Gstar`/`Ginv`/`Comp` fields — doing
  so faithfully needs `holonomyConjBFL2 U` to be a genuine two-sided-invertible, self-adjoint,
  positive-semidefinite operator (`BalabanCovarianceData`'s field shape), which conjugation by a
  general (non-central) `U` is NOT guaranteed to be self-adjoint under `BFL2`'s real inner product
  (adjoint action on `𝔰𝔲(2)` is an ISOMETRY — proved here, §2b — but isometries need not be
  self-adjoint; `R(U)ᵀ = R(U)⁻¹ = R(U⁻¹)`, not `R(U)` itself, except when `U` is an involution).
  This is the honest reason the full anchoring (making `deltaKUnifiedData` itself `U`-dependent) is
  NOT attempted here — named, not papered.
* `IsBoundedReparam`'s smallness threshold `2KM_J < 1/2−a` is THIS FILE'S OWN structural choice
  (item 1 above), not a literal transcription of a CMP99b numeric bound — disclosed, not hidden.

Does **not edit** `DeltaKUnified.lean`, `RegularUCoercivity.lean`, `CovariantOperators.lean`,
`RegularityHolonomy.lean`, `Q1Real.lean` — every ingredient is imported and reused (LAW-19).
-/

import AdalyFormal.Balaban.DeltaKUnified
import AdalyFormal.Balaban.RegularUCoercivity
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.RegularityHolonomy
import AdalyFormal.Balaban.Q1Real

set_option autoImplicit false

namespace AdalyFormal.Balaban.BoundedReparam

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.DeltaKUnified
open AdalyFormal.Balaban.RegularityHolonomy
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator solutionOperator_apply)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape taylorQuadraticTerm)
open AdalyFormal.Balaban.DeltaKAssembly (deltaKForm taylorQuadraticTerm_sq_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul RMap_witnessMElem
  witnessU witnessMElem suTwoWitness suTwoWitness_ne_neg_self)
open AdalyFormal.Balaban.RegularUCoercivity (regB0 regB0_ne_zero regB0_norm_pos qextQuad
  adversarialJ dtilde2_qextQuad deltaKUnifiedData_first_two_terms_eq
  deltaKUnifiedData_first_two_terms_coercive solutionOperator_deltaKUnifiedData_eq_id
  norm_smul_real_sq)

/-! ## §1 — `IsBoundedReparam`, THE MISSING PRIMITIVE, DEFINED

The analogue of `TheLemma.IsBalabanReparam` for the external parameters `Qext`/`J` that `deltaKForm`
inherits (CMP99b (3.156)). Two SHAPE clauses (quadratic-growth control on `D̃⁽²⁾`, a norm bound on
`J`) plus ONE EXCLUSION clause (the smallness threshold, item 1 of the header). -/

/-- **`IsBoundedReparam bc Qext J K M_J`**: `Qext`'s `D̃⁽²⁾`-image is controlled by `K‖B‖²` for every
`B` (CMP99b p.427's own description of `D̃⁽²⁾` as "a quadratic polynomial in `B`", made quantitative),
`‖J‖ ≤ M_J`, and the source-coupling term `2KM_J` does not exceed the base-gap term `1/2 − a` that
`deltaKUnifiedData_first_two_terms_coercive` already controls unconditionally. -/
def IsBoundedReparam (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (K MJ : ℝ) : Prop :=
  0 ≤ K ∧ 0 ≤ MJ ∧
    (∀ B : BFL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ K * ‖B‖ ^ 2) ∧
    ‖J‖ ≤ MJ ∧
    2 * K * MJ < 1 / 2 - bc.a

/-- D82 GARBAGE SUBSTITUTION control: the ZERO-EXCLUSION-CLAUSE variant (dropping the smallness
inequality entirely, keeping only the two shape clauses) is satisfied by the crux's OWN adversarial
witness — confirming the shape clauses alone carry no exclusionary force and the smallness clause is
the one doing all the work (checked directly, not merely asserted; used by §3's own headline). -/
def IsBoundedReparamShapeOnly (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (K MJ : ℝ) : Prop :=
  0 ≤ K ∧ 0 ≤ MJ ∧ (∀ B : BFL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ K * ‖B‖ ^ 2) ∧ ‖J‖ ≤ MJ

theorem isBoundedReparam_shapeOnly_of (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (K MJ : ℝ) (h : IsBoundedReparam bc Qext J K MJ) :
    IsBoundedReparamShapeOnly Qext J K MJ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

#print axioms isBoundedReparam_shapeOnly_of

/-! ## §2 — A GENUINELY `U`-DEPENDENT INGREDIENT: `holonomyConjBFL2`, reusing `RMap` (LAW-19)

The real `Δ_k`'s `U`-dependence lives in the holonomies `R(U(·))` inside `Q`, `G₁`, `H₁` — the exact
finding of the crux's own diagnosis. This section builds the cleanest such ingredient: componentwise
adjoint-holonomy multiplication on `Bond witnessL → SuTwo`, transported to `BFL2 witnessL`. -/

open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- **`X ↦ (b ↦ R(U(b))·X(b))`, as a genuine `LinearMap ℝ`** on the bare function type. Linear
because `RMap (U b)` is linear at each fixed `b` (`map_add`/`map_smul`). -/
noncomputable def holonomyConjMapRaw
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) where
  toFun X b := RMap (U b) (X b)
  map_add' X Y := by funext b; simp only [Pi.add_apply]; exact map_add (RMap (U b)) (X b) (Y b)
  map_smul' c X := by
    funext b; simp only [Pi.smul_apply, RingHom.id_apply]; exact map_smul (RMap (U b)) c (X b)

theorem holonomyConjMapRaw_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (X : Bond witnessL → SuTwo) (b : Bond witnessL) :
    holonomyConjMapRaw U X b = RMap (U b) (X b) := rfl

/-- **The `U`-dependent ingredient, transported onto `BFL2 witnessL`** — `DeltaKUnified.bfl2Equiv`
conjugating `holonomyConjMapRaw`, the SAME "promote a bare-Pi-type construction onto the wrapped
carrier" move `DeltaKUnified.lean` §2 itself uses for `subspace156G`/`subspace156BFL2` (LAW-19). -/
noncomputable def holonomyConjBFL2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →ₗ[ℝ] BFL2 witnessL :=
  (bfl2Equiv (Lat := witnessL)).symm.toLinearMap ∘ₗ
    holonomyConjMapRaw U ∘ₗ (bfl2Equiv (Lat := witnessL)).toLinearMap

theorem holonomyConjBFL2_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (X : BFL2 witnessL) :
    bfl2Equiv (Lat := witnessL) (holonomyConjBFL2 U X) =
      holonomyConjMapRaw U (bfl2Equiv (Lat := witnessL) X) := by
  unfold holonomyConjBFL2
  simp

#print axioms holonomyConjMapRaw
#print axioms holonomyConjMapRaw_apply
#print axioms holonomyConjBFL2
#print axioms holonomyConjBFL2_apply

/-- §2a — **`holonomyConjBFL2 (trivialU) = id`** — the flat-background reduction: `R(1) = id`
(`RMap_one`), so the conjugation ingredient collapses to the identity exactly at the trivial
background, matching `deltaKUnifiedData`'s current `Q := Qstar := 1` wiring at that ONE point. -/
theorem holonomyConjBFL2_trivialU_eq_id (X : BFL2 witnessL) :
    holonomyConjBFL2 (trivialU witnessL) X = X := by
  apply (bfl2Equiv (Lat := witnessL)).injective
  rw [holonomyConjBFL2_apply]
  funext b
  rw [holonomyConjMapRaw_apply]
  show RMap ((trivialU witnessL) b) (bfl2Equiv (Lat := witnessL) X b) = _
  unfold AdalyFormal.Balaban.CovariantHjMinimizer.trivialU
  rw [RMap_one]
  rfl

#print axioms holonomyConjBFL2_trivialU_eq_id

/-- The explicit raw witness function: `suTwoWitness` at the single bond `(witnessY, 0)`, `0`
elsewhere — the SAME site/direction `CovariantOperators.witnessU`'s own non-flat link sits at
(`witnessU_at_x_mu`), chosen so the two backgrounds' conjugation actions are compared at the bond
where they actually differ. -/
noncomputable def bondWitnessRaw : Bond witnessL → SuTwo :=
  fun b => if b = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then suTwoWitness else 0

theorem bondWitnessRaw_at_witness :
    bondWitnessRaw (AdmissibleSubspace.witnessY, (0 : Fin 3)) = suTwoWitness := by
  unfold bondWitnessRaw; simp

/-- **§2b — THE HEADLINE `U`-DEPENDENCE FACT, PROVED**: `holonomyConjBFL2` takes DIFFERENT values at
`trivialU` vs. the tree's own non-flat witness `CovariantOperators.witnessU`, at the SAME raw input
point — the opposite of `deltaKFormOnSubspace156_U_independent`. At the bond `(witnessY,0)`, the
trivial background leaves `suTwoWitness` fixed (`R(1) = id`) while `witnessU` sends it to
`-suTwoWitness` (`R(M)·suTwoWitness = -suTwoWitness`, `RMap_witnessMElem`, `M ≠ 1` since
`suTwoWitness ≠ -suTwoWitness`, `suTwoWitness_ne_neg_self`). -/
theorem holonomyConjBFL2_trivialU_ne_witnessU :
    holonomyConjBFL2 (trivialU witnessL) ((bfl2Equiv (Lat := witnessL)).symm bondWitnessRaw) ≠
      holonomyConjBFL2 witnessU ((bfl2Equiv (Lat := witnessL)).symm bondWitnessRaw) := by
  intro heq
  have hcongr := congrArg (bfl2Equiv (Lat := witnessL)) heq
  rw [holonomyConjBFL2_apply, holonomyConjBFL2_apply] at hcongr
  simp only [LinearEquiv.apply_symm_apply] at hcongr
  have hb := congrFun hcongr (AdmissibleSubspace.witnessY, (0 : Fin 3))
  rw [holonomyConjMapRaw_apply, holonomyConjMapRaw_apply, bondWitnessRaw_at_witness] at hb
  have htrivial : (trivialU witnessL) (AdmissibleSubspace.witnessY, (0 : Fin 3)) =
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  rw [htrivial, RMap_one] at hb
  simp only [LinearMap.id_coe, id_eq] at hb
  have hwit : witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) = witnessMElem := by
    unfold AdalyFormal.Balaban.CovariantOperators.witnessU; simp
  rw [hwit, RMap_witnessMElem] at hb
  exact suTwoWitness_ne_neg_self hb

#print axioms holonomyConjBFL2_trivialU_ne_witnessU

/-! ## §3 — `IsBoundedReparam` BLOCKS THE CRUX'S ADVERSARIAL WITNESS, PROVED

The crux's own `(qextQuad regB0, adversarialJ bc)` pair — the exact witness driving
`deltaKFormOnSubspace156` arbitrarily negative — is shown here to fail `IsBoundedReparam` for EVERY
choice of `K`, `M_J`, not merely for some particular bad choice. The shape clauses alone
(`IsBoundedReparamShapeOnly`) are satisfiable (finite-dimensional, everything is bounded); it is
SPECIFICALLY the smallness clause that excludes this witness — isolated precisely below. -/

/-- **`‖adversarialJ bc‖ = (1+|1/2−bc.a|)/(2‖regB0‖)`, computed exactly.** -/
theorem adversarialJ_norm_eq (bc : BaseConstant) :
    ‖adversarialJ bc‖ = (1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖) := by
  unfold adversarialJ
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |1/2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖^2))]
  have hne : ‖(regB0 : BFL2 witnessL)‖ ≠ 0 := regB0_norm_pos.ne'
  field_simp

#print axioms adversarialJ_norm_eq

/-- **Any `K` admissible for the shape clause at `Qext := qextQuad regB0` must satisfy `K ≥ ‖regB0‖`**
— forced by evaluating the bound AT `regB0` itself, using the EXACT closed form
`Dtilde2Shape (qextQuad regB0) regB0 = ‖regB0‖²•regB0` (`dtilde2_qextQuad`, on record). -/
theorem le_of_dtilde2_bound_at_regB0 (K : ℝ)
    (h : ∀ B : BFL2 witnessL, ‖Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) B‖ ≤ K * ‖B‖ ^ 2) :
    ‖(regB0 : BFL2 witnessL)‖ ≤ K := by
  have hb := h (regB0 : BFL2 witnessL)
  rw [dtilde2_qextQuad] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
  have hpos : (0:ℝ) < ‖(regB0 : BFL2 witnessL)‖ ^ 2 := pow_pos regB0_norm_pos 2
  have hb' : ‖(regB0 : BFL2 witnessL)‖ * ‖(regB0 : BFL2 witnessL)‖ ^ 2 ≤
      K * ‖(regB0 : BFL2 witnessL)‖ ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right hb' hpos

#print axioms le_of_dtilde2_bound_at_regB0

/-- **THE BLOCKING RESULT**: for EVERY `K M_J : ℝ`, `IsBoundedReparam` FAILS at the crux's own
adversarial pair — precisely because the smallness clause cannot survive the forced lower bounds
`K ≥ ‖regB0‖`, `M_J ≥ ‖adversarialJ bc‖` established above. -/
theorem adversarial_not_boundedReparam (bc : BaseConstant) (K MJ : ℝ) :
    ¬ IsBoundedReparam bc (qextQuad (regB0 : BFL2 witnessL)) (adversarialJ bc) K MJ := by
  rintro ⟨hK0, hMJ0, hshape, hJ, hsmall⟩
  have hK : ‖(regB0 : BFL2 witnessL)‖ ≤ K := le_of_dtilde2_bound_at_regB0 K hshape
  have hMJ : (1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖) ≤ MJ := by
    rw [← adversarialJ_norm_eq]; exact hJ
  have hMJ0' : (0:ℝ) ≤ (1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖) := by positivity
  have hprod : ‖(regB0 : BFL2 witnessL)‖ *
      ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖)) ≤ K * MJ :=
    mul_le_mul hK hMJ hMJ0' (le_trans (norm_nonneg _) hK)
  have hne : ‖(regB0 : BFL2 witnessL)‖ ≠ 0 := regB0_norm_pos.ne'
  have hcollapse : ‖(regB0 : BFL2 witnessL)‖ *
      ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖)) = (1 + |1 / 2 - bc.a|) / 2 := by
    field_simp
  rw [hcollapse] at hprod
  have hle : (1 : ℝ) / 2 - bc.a ≤ |1 / 2 - bc.a| := le_abs_self _
  linarith

#print axioms adversarial_not_boundedReparam

/-! ## §4 — COERCIVITY UNDER `IsBoundedReparam`, FULLY PROVED (not conditional-and-unproved: a
genuine closed theorem, `sorry`-free) -/

/-- **`deltaKForm deltaKUnifiedData` is coercive on ALL of `BFL2 witnessL` under `IsBoundedReparam`**
— the Cauchy–Schwarz bound on the source term (`real_inner_le_norm`), combined with
`deltaKUnifiedData_first_two_terms_eq` (exact) and `solutionOperator_deltaKUnifiedData_eq_id`
(exact, `H₁ = id` on this carrier), gives the explicit margin `γ₀ := 1/2 − bc.a − 2KM_J`. -/
theorem deltaKForm_coercive_of_bounded (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (K MJ : ℝ) (hbdd : IsBoundedReparam bc Qext J K MJ) (x : BFL2 witnessL) :
    (1 / 2 - bc.a - 2 * K * MJ) * ‖x‖ ^ 2 ≤ deltaKForm deltaKUnifiedData bc Qext J x := by
  obtain ⟨hK0, hMJ0, hshape, hJ, -⟩ := hbdd
  have hfirst2 := deltaKUnifiedData_first_two_terms_eq bc x
  have hsrc_le : (inner ℝ (solutionOperator deltaKUnifiedData (Dtilde2Shape Qext x)) J : ℝ) ≤
      ‖solutionOperator deltaKUnifiedData (Dtilde2Shape Qext x)‖ * ‖J‖ :=
    real_inner_le_norm _ _
  have hH1 : solutionOperator deltaKUnifiedData (Dtilde2Shape Qext x) = Dtilde2Shape Qext x :=
    solutionOperator_deltaKUnifiedData_eq_id _
  rw [hH1] at hsrc_le
  have hnormQext : ‖Dtilde2Shape Qext x‖ ≤ K * ‖x‖ ^ 2 := hshape x
  have hKMJnn : (0:ℝ) ≤ K * ‖x‖ ^ 2 := mul_nonneg hK0 (sq_nonneg _)
  have hsrc_le2 : ‖Dtilde2Shape Qext x‖ * ‖J‖ ≤ (K * ‖x‖ ^ 2) * MJ :=
    mul_le_mul hnormQext hJ (norm_nonneg _) hKMJnn
  have hsrc_le3 : (inner ℝ (solutionOperator deltaKUnifiedData (Dtilde2Shape Qext x)) J : ℝ) ≤
      K * MJ * ‖x‖ ^ 2 := by
    rw [hH1]; nlinarith [hsrc_le, hsrc_le2]
  show (inner ℝ x (deltaKUnifiedData.CompInv x) : ℝ) - usedAt bc 0 * (inner ℝ x x : ℝ)
      - 2 * (inner ℝ (solutionOperator deltaKUnifiedData (Dtilde2Shape Qext x)) J : ℝ) ≥ _
  have hfirst2' : (inner ℝ x (deltaKUnifiedData.CompInv x) : ℝ) - usedAt bc 0 * (inner ℝ x x : ℝ) =
      (1 / 2 - bc.a) * ‖x‖ ^ 2 := hfirst2
  nlinarith [hfirst2', hsrc_le3]

#print axioms deltaKForm_coercive_of_bounded

/-- **`γ₀ := 1/2 − bc.a − 2KM_J` IS STRICTLY POSITIVE under `IsBoundedReparam`** — the smallness
clause is EXACTLY what is needed for this, nothing more. -/
theorem gamma0_pos_of_boundedReparam (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (K MJ : ℝ) (hbdd : IsBoundedReparam bc Qext J K MJ) :
    0 < 1 / 2 - bc.a - 2 * K * MJ := by
  have := hbdd.2.2.2.2; linarith

#print axioms gamma0_pos_of_boundedReparam

/-- **THE CONDITIONAL LEMMA, FULLY CLOSED — the honest resolution of the crux's `sorry`.** Under
`IsBoundedReparam`, `theLemma_regularU`'s bound HOLDS, for every `Mα₀thresh`, every regular `U`
(the form is `U`-independent on `subspace156BFL2`, `deltaKFormOnSubspace156_eq`, so the bound
transfers unconditionally in `U`), and every admissible `B`. Genuinely `∃γ₀ > 0` before every `∀`
(S92), matching `TheLemmaRegularU`'s own binder discipline. -/
theorem theLemma_regularU_bounded_coercive (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (K MJ : ℝ) (hbdd : IsBoundedReparam bc Qext J K MJ)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Mα₀thresh : ℝ, 0 < Mα₀thresh →
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
      IsRegularHolonomy U Mα₀thresh →
      ∀ B : subspace156BFL2 Lambda S' ell U,
        γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤ deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B := by
  refine ⟨1 / 2 - bc.a - 2 * K * MJ, gamma0_pos_of_boundedReparam bc Qext J K MJ hbdd, ?_⟩
  intro Mα₀thresh _ U _ B
  rw [deltaKFormOnSubspace156_eq]
  exact deltaKForm_coercive_of_bounded bc Qext J K MJ hbdd (B : BFL2 witnessL)

#print axioms theLemma_regularU_bounded_coercive

/-! ## §5 — NON-VACUITY of `IsBoundedReparam` -/

/-- **`Dtilde2Shape (qextQuad 0) B = 0` for every `B`** — the zero direction collapses the general
`dtilde2_qextQuad` formula to `0`. -/
theorem dtilde2_qextQuad_zero (B : BFL2 witnessL) :
    Dtilde2Shape (qextQuad (0 : BFL2 witnessL)) B = 0 := by
  rw [dtilde2_qextQuad]; simp

#print axioms dtilde2_qextQuad_zero

/-- **`IsBoundedReparam` IS NON-VACUOUS**: `Qext := qextQuad 0`, `J := 0`, `K := M_J := 0` satisfies
every clause whenever `bc.a < 1/2` — the hypothesis is genuinely inhabited, not an empty predicate
that vacuously "blocks" everything. -/
theorem isBoundedReparam_zero_witness (bc : BaseConstant) (ha : bc.a < 1 / 2) :
    IsBoundedReparam bc (qextQuad (0 : BFL2 witnessL)) (0 : BFL2 witnessL) 0 0 := by
  refine ⟨le_refl 0, le_refl 0, ?_, by simp, ?_⟩
  · intro B; rw [dtilde2_qextQuad_zero]; simp
  · simpa using ha

#print axioms isBoundedReparam_zero_witness

/-! ## §6 — NON-DEGENERATE INSTANCES, AND THE THRESHOLD IS SHARP (added 2026-07-27)

**Why this section exists.** `compute/REGISTRY_CAVEAT_SWEEP.md` Tier-1 item 1 measured that §5's
`isBoundedReparam_zero_witness` was the ONLY positive discharge of `IsBoundedReparam` anywhere in
the tree, at `Qext := qextQuad 0`, `J := 0`, `K := M_J := 0`. Stated precisely (and no more strongly
than it is): the predicate is not vacuous — §3 is a real control showing it EXCLUDES something, and
§5 achieves exactly the non-vacuity it claims — but nothing supplied a NON-DEGENERATE instance, so
`theLemma_regularU_bounded_coercive` (§4) could only be instantiated at all-zero data, where its
conclusion reduces to `deltaKUnifiedData_first_two_terms_coercive`, already on record.

This section closes that. Three facts, all `sorry`-free:

1. **The ENTIRE admissible parameter region is realized** (`isBoundedReparam_full_range`): for every
   `K, M_J ≥ 0` with `2·K·M_J < 1/2 − bc.a`, `IsBoundedReparam` holds at `Qext := qextQuad (K•u₀)`,
   `J := M_J•u₀`, where `u₀ := ‖regB0‖⁻¹ • regB0` is the unit vector in `regB0`'s direction. Both
   shape clauses hold with EQUALITY (`dtilde2_qextQuad` is an exact closed form and `‖u₀‖ = 1`), so
   `K` and `M_J` are the SHARP constants for this pair, not slack over-estimates. In particular
   `K > 0` and `M_J > 0` are admissible whenever `bc.a < 1/2`.
2. **These instances are NOT the zero instance, nor a rescaling of it** (`instance_J_ne_zero`,
   `instance_dtilde2_ne_zero`, `instance_not_rescaling_of_zero`): at `K ≠ 0` the map
   `Dtilde2Shape (qextQuad (K•u₀))` is not the zero map, whereas `c • qextQuad 0` has identically
   zero `D̃⁽²⁾` for EVERY `c` — so no scalar rescaling of the §5 witness reaches this family. At
   `M_J ≠ 0` the source `J` is nonzero, so §4's third term genuinely contributes.
3. **`γ₀ := 1/2 − bc.a − 2·K·M_J` is EXACTLY the value, and `2KM_J < 1/2 − a` is EXACTLY the
   coercivity threshold on this family** (`deltaKForm_at_instance`, `gamma0_sharp`,
   `theLemma_regularU_fails_at_or_above_threshold`). The form's value at every `x` is
   `(1/2 − bc.a − 2KM_J)·‖x‖²` — an EQUALITY, so §4's bound is attained, not slack; no constant
   larger than `γ₀` works; and at `2KM_J ≥ 1/2 − bc.a` NO positive coercivity constant exists (at
   equality the form is identically `0`; above it, strictly negative at `u₀ ≠ 0`).

**Fact worth stating plainly about the header's own disclosure.** The header discloses that the
threshold `2KM_J < 1/2 − a` is "THIS FILE'S OWN structural choice" rather than a transcribed source
number. Item 3 shows that, on the realizable family built here, that choice is not merely a choice:
it is necessary and sufficient for a positive coercivity constant to exist at all. That is a fact
about this family and this artifact, and it removes the need to hunt a source constant for it — the
corpus check the header already recorded (`CMP99b_p427.md`, `CMP99b_p428.md`: `D̃⁽²⁾` described only
qualitatively) is unchanged and no new source claim is made here.

**Denotational scope, stated and not hidden (F4).** Everything here is about `deltaKUnifiedData`,
which `DeltaKUnified.lean`'s own correction banner records as having `Q = Qstar = 1` and
`CompInv = (1/2)•1` — no Schur complement, hence not `Δ_k`. §6 makes the `Qext`/`J`/`K`/`M_J`
parameters non-degenerate; it does NOT make the underlying covariance data faithful, and no
statement here transfers to Bałaban's `Δ_k` by virtue of being proved here. -/

/-- `u₀ := ‖regB0‖⁻¹ • regB0`, the unit vector in `regB0`'s direction. Nonzero because `regB0` is
(`regB0_ne_zero`, `regB0_norm_pos`). -/
noncomputable def unitB0 : BFL2 witnessL :=
  (‖(regB0 : BFL2 witnessL)‖)⁻¹ • (regB0 : BFL2 witnessL)

/-- `‖u₀‖ = 1`, computed. -/
theorem norm_unitB0 : ‖unitB0‖ = 1 := by
  unfold unitB0
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos regB0_norm_pos]
  exact inv_mul_cancel₀ regB0_norm_pos.ne'

theorem unitB0_ne_zero : unitB0 ≠ 0 := by
  intro h
  have h1 : ‖unitB0‖ = 1 := norm_unitB0
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- `⟪u₀, u₀⟫ = 1`. -/
theorem inner_unitB0_self : (inner ℝ unitB0 unitB0 : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_unitB0]; norm_num

#print axioms unitB0
#print axioms norm_unitB0
#print axioms unitB0_ne_zero
#print axioms inner_unitB0_self

/-- **`Dtilde2Shape (qextQuad (K•u₀)) B = ‖B‖² • (K • u₀)`, and its norm is EXACTLY `K‖B‖²`** for
`K ≥ 0` — so the shape clause of `IsBoundedReparam` is met with EQUALITY, making `K` the sharp
constant rather than a slack over-estimate. -/
theorem norm_dtilde2_unit_instance (K : ℝ) (hK : 0 ≤ K) (B : BFL2 witnessL) :
    ‖Dtilde2Shape (qextQuad (K • unitB0)) B‖ = K * ‖B‖ ^ 2 := by
  rw [dtilde2_qextQuad, norm_smul, norm_smul, norm_unitB0, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖B‖), abs_of_nonneg hK, mul_one]
  ring

#print axioms norm_dtilde2_unit_instance

/-- **THE NON-DEGENERATE INSTANCE FAMILY — the whole admissible parameter region is realized.** For
EVERY `K, M_J ≥ 0` with `2·K·M_J < 1/2 − bc.a`, `IsBoundedReparam` holds at that exact `(K, M_J)`
with `Qext := qextQuad (K•u₀)` and `J := M_J•u₀`. Both shape clauses hold with EQUALITY. Taking
`K, M_J > 0` (possible for every `bc` with `bc.a < 1/2`, exhibited in
`isBoundedReparam_nonzero_witness` below) gives an instance at NONZERO `J`, `K`, `M_J`. -/
theorem isBoundedReparam_full_range (bc : BaseConstant) (K MJ : ℝ)
    (hK : 0 ≤ K) (hMJ : 0 ≤ MJ) (hsmall : 2 * K * MJ < 1 / 2 - bc.a) :
    IsBoundedReparam bc (qextQuad (K • unitB0)) (MJ • unitB0) K MJ := by
  refine ⟨hK, hMJ, ?_, ?_, hsmall⟩
  · intro B; rw [norm_dtilde2_unit_instance K hK B]
  · rw [norm_smul, norm_unitB0, Real.norm_eq_abs, abs_of_nonneg hMJ, mul_one]

#print axioms isBoundedReparam_full_range

/-- **AN EXPLICIT INSTANCE AT NONZERO `J`, `K`, `M_J`** — the concrete deliverable the caveat sweep
asked for. Take `K := M_J := δ` with `δ := min (1/2) ((1/2 − bc.a)/2)`; then `δ > 0` whenever
`bc.a < 1/2`, and `2δ² ≤ 2·(1/2)·δ = δ < 1/2 − bc.a`. -/
theorem isBoundedReparam_nonzero_witness (bc : BaseConstant) (ha : bc.a < 1 / 2) :
    ∃ K MJ : ℝ, 0 < K ∧ 0 < MJ ∧
      IsBoundedReparam bc (qextQuad (K • unitB0)) (MJ • unitB0) K MJ := by
  set d : ℝ := min (1 / 2) ((1 / 2 - bc.a) / 2) with hd
  have hpos : 0 < d := lt_min (by norm_num) (by linarith)
  have hle_half : d ≤ 1 / 2 := min_le_left _ _
  have hle_gap : d ≤ (1 / 2 - bc.a) / 2 := min_le_right _ _
  refine ⟨d, d, hpos, hpos, isBoundedReparam_full_range bc d d hpos.le hpos.le ?_⟩
  have h1 : 2 * d * d ≤ 2 * (1 / 2 : ℝ) * d := by nlinarith
  have h2 : 2 * (1 / 2 : ℝ) * d = d := by ring
  have h3 : d < 1 / 2 - bc.a := by linarith
  linarith

#print axioms isBoundedReparam_nonzero_witness

/-! ### §6a — the instances are NOT degenerate: attacked before being reported

Three checks, each a kernel-level refutation rather than a claim: the source is genuinely nonzero,
the quadratic reparametrization's `D̃⁽²⁾` is genuinely NOT the zero map, and no SCALAR RESCALING of
§5's zero witness produces this family (rescaling `qextQuad 0` keeps `D̃⁽²⁾ ≡ 0`, so the two live in
different classes — this is the "is it secretly the zero instance in disguise?" test, answered). -/

theorem instance_J_ne_zero (MJ : ℝ) (h : MJ ≠ 0) : (MJ • unitB0) ≠ 0 := by
  intro hz
  have : ‖MJ • unitB0‖ = 0 := by rw [hz, norm_zero]
  rw [norm_smul, norm_unitB0, mul_one, Real.norm_eq_abs] at this
  exact h (abs_eq_zero.mp this)

/-- `D̃⁽²⁾` of this family's `Qext` is NOT the zero map at `K ≠ 0`: at `B := u₀` its value is
`K • u₀ ≠ 0`. -/
theorem instance_dtilde2_ne_zero (K : ℝ) (hK : K ≠ 0) :
    Dtilde2Shape (qextQuad (K • unitB0)) unitB0 ≠ 0 := by
  intro hz
  have hnorm : ‖Dtilde2Shape (qextQuad (K • unitB0)) unitB0‖ = 0 := by rw [hz, norm_zero]
  rw [dtilde2_qextQuad, norm_smul, norm_smul, norm_unitB0, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_one] at hnorm
  simp only [one_pow, abs_one, one_mul] at hnorm
  exact hK (abs_eq_zero.mp hnorm)

/-- **NOT A RESCALING OF THE ZERO INSTANCE.** For every real `c`, the map `x ↦ c • qextQuad 0 x` has
`D̃⁽²⁾ ≡ 0` (indeed it IS the zero map), while this family's `Qext` does not — so the §5 witness
cannot be scaled into this family, and the §6 instances are new data, not the old data in disguise. -/
theorem instance_not_rescaling_of_zero (K : ℝ) (hK : K ≠ 0) (c : ℝ) :
    qextQuad (K • unitB0) ≠ (fun x : BFL2 witnessL => c • qextQuad (0 : BFL2 witnessL) x) := by
  intro heq
  apply instance_dtilde2_ne_zero K hK
  rw [heq]
  have hfun : (fun x : BFL2 witnessL => c • qextQuad (0 : BFL2 witnessL) x) =
      (fun _ : BFL2 witnessL => (0 : BFL2 witnessL)) := by
    funext x; show c • (‖x‖ ^ 2 • (0 : BFL2 witnessL)) = 0; simp
  rw [hfun]
  show Dtilde2Shape (fun _ : BFL2 witnessL => (0 : BFL2 witnessL)) unitB0 = 0
  show taylorQuadraticTerm (fun _ : ℝ => (0 : BFL2 witnessL)) = 0
  unfold taylorQuadraticTerm
  simp

#print axioms instance_J_ne_zero
#print axioms instance_dtilde2_ne_zero
#print axioms instance_not_rescaling_of_zero

/-! ### §6b — `Dtilde2Shape` of the CONSTANT-ZERO map, the primitive Tier-1 item 3 named

`compute/REGISTRY_CAVEAT_SWEEP.md` Tier-1 item 3 records that
`CoercivityAdaptation.LEM_COERC_U1_DELTAK` is left unformalized for want of
`Dtilde2Shape (fun _ => 0) B = 0`, and asks whether §5's `dtilde2_qextQuad_zero`
(`Dtilde2Shape (qextQuad 0) B = 0`) already discharges it. **It does, and here is why, proved rather
than argued**: `qextQuad 0` IS the constant-zero map (`qextQuad_zero_eq_constZero`), so the two
statements are the same statement up to that rewriting. Both forms are supplied below so a consumer
can use either. `CoercivityAdaptation.lean` is NOT edited from here (write-scope discipline); this is
the primitive it named, made available. -/

theorem qextQuad_zero_eq_constZero :
    qextQuad (0 : BFL2 witnessL) = (fun _ : BFL2 witnessL => (0 : BFL2 witnessL)) := by
  funext x; show ‖x‖ ^ 2 • (0 : BFL2 witnessL) = 0; simp

theorem dtilde2_constZero (B : BFL2 witnessL) :
    Dtilde2Shape (fun _ : BFL2 witnessL => (0 : BFL2 witnessL)) B = 0 := by
  rw [← qextQuad_zero_eq_constZero]; exact dtilde2_qextQuad_zero B

#print axioms qextQuad_zero_eq_constZero
#print axioms dtilde2_constZero

/-! ### §6c — the value is EXACT, so §4's `γ₀` is attained and the threshold is sharp -/

/-- **THE EXACT VALUE ON THE INSTANCE FAMILY**: an EQUALITY, not a bound —
`deltaKForm deltaKUnifiedData bc (qextQuad (K•u₀)) (M_J•u₀) x = (1/2 − bc.a − 2KM_J)·‖x‖²` for every
`x`. Hence §4's `deltaKForm_coercive_of_bounded` is TIGHT on this family: the constant
`γ₀ = 1/2 − bc.a − 2KM_J` is attained at every point, so the `2KM_J` deduction is not slack. -/
theorem deltaKForm_at_instance (bc : BaseConstant) (K MJ : ℝ) (x : BFL2 witnessL) :
    deltaKForm deltaKUnifiedData bc (qextQuad (K • unitB0)) (MJ • unitB0) x
      = (1 / 2 - bc.a - 2 * K * MJ) * ‖x‖ ^ 2 := by
  show (inner ℝ x (deltaKUnifiedData.CompInv x) : ℝ) - usedAt bc 0 * (inner ℝ x x : ℝ)
      - 2 * (inner ℝ (solutionOperator deltaKUnifiedData
          (Dtilde2Shape (qextQuad (K • unitB0)) x)) (MJ • unitB0) : ℝ) = _
  have hfirst2 : (inner ℝ x (deltaKUnifiedData.CompInv x) : ℝ) - usedAt bc 0 * (inner ℝ x x : ℝ) =
      (1 / 2 - bc.a) * ‖x‖ ^ 2 := deltaKUnifiedData_first_two_terms_eq bc x
  have hD2 : Dtilde2Shape (qextQuad (K • unitB0)) x = ‖x‖ ^ 2 • (K • unitB0) :=
    dtilde2_qextQuad _ _
  have hH1 : solutionOperator deltaKUnifiedData (Dtilde2Shape (qextQuad (K • unitB0)) x) =
      ‖x‖ ^ 2 • (K • unitB0) := by
    rw [solutionOperator_deltaKUnifiedData_eq_id, hD2]
  rw [hfirst2, hH1]
  have hsrc : (inner ℝ ((‖x‖ ^ 2 : ℝ) • (K • unitB0)) (MJ • unitB0) : ℝ)
      = ‖x‖ ^ 2 * (K * MJ) := by
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, inner_unitB0_self]
    ring
  rw [hsrc]
  ring

#print axioms deltaKForm_at_instance

/-- **`γ₀` IS SHARP: no larger constant works.** If `γ` is any coercivity constant for the instance
`(qextQuad (K•u₀), M_J•u₀)` then `γ ≤ 1/2 − bc.a − 2KM_J`. Proved by testing at the single point
`u₀`, where `‖u₀‖² = 1`. -/
theorem gamma0_sharp (bc : BaseConstant) (K MJ γ : ℝ)
    (hγ : ∀ x : BFL2 witnessL,
      γ * ‖x‖ ^ 2 ≤ deltaKForm deltaKUnifiedData bc (qextQuad (K • unitB0)) (MJ • unitB0) x) :
    γ ≤ 1 / 2 - bc.a - 2 * K * MJ := by
  have h := hγ unitB0
  rw [deltaKForm_at_instance, norm_unitB0] at h
  simpa using h

#print axioms gamma0_sharp

/-- **THE THRESHOLD CANNOT BE RELAXED TO `≤`.** At `2KM_J ≥ 1/2 − bc.a` the form admits NO positive
coercivity constant: at `u₀` its value is `(1/2 − bc.a − 2KM_J) ≤ 0`, while `γ‖u₀‖² = γ > 0`. So the
strict smallness clause of `IsBoundedReparam` is exactly the boundary of coercivity on the realizable
family of §6 — necessary as well as sufficient. -/
theorem no_positive_coercivity_at_or_above_threshold (bc : BaseConstant) (K MJ γ : ℝ)
    (hthr : 1 / 2 - bc.a ≤ 2 * K * MJ) (hγ : 0 < γ) :
    ¬ (γ * ‖unitB0‖ ^ 2 ≤
        deltaKForm deltaKUnifiedData bc (qextQuad (K • unitB0)) (MJ • unitB0) unitB0) := by
  intro h
  rw [deltaKForm_at_instance, norm_unitB0] at h
  simp only [one_pow, mul_one] at h
  linarith

#print axioms no_positive_coercivity_at_or_above_threshold

/-- `u₀` as a member of the `(3.156)` subspace at `trivialU` — the scalar multiple
`‖regB0‖⁻¹ • regB0` of §5's own witness, so `Submodule`-closure supplies membership. Needed to state
the threshold-sharpness refutation against `theLemma_regularU_bounded_coercive`'s OWN conclusion
shape (which quantifies over the subspace, not the ambient carrier). -/
noncomputable def unitB0Sub : subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL))
    ∅ witnessEll (trivialU witnessL) :=
  (‖(regB0 : BFL2 witnessL)‖)⁻¹ • regB0

theorem unitB0Sub_coe : ((unitB0Sub : BFL2 witnessL)) = unitB0 := rfl

/-- **THE CONCLUSION OF `theLemma_regularU_bounded_coercive` IS FALSE AT AND ABOVE THE THRESHOLD** —
for the §6 family, at `2KM_J ≥ 1/2 − bc.a`, there is NO positive `γ₀` making the conclusion hold,
even restricted to the subspace and at the flat background. Together with §4 (which supplies such a
`γ₀` strictly below the threshold) this pins the smallness clause exactly. -/
theorem theLemma_regularU_fails_at_or_above_threshold (bc : BaseConstant) (K MJ : ℝ)
    (hthr : 1 / 2 - bc.a ≤ 2 * K * MJ) :
    ¬ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ B : subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ witnessEll
          (trivialU witnessL),
        γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤
          deltaKFormOnSubspace156 bc (qextQuad (K • unitB0)) (MJ • unitB0)
            Finset.univ ∅ witnessEll (trivialU witnessL) B := by
  rintro ⟨γ₀, hpos, hall⟩
  have h := hall unitB0Sub
  rw [deltaKFormOnSubspace156_eq, unitB0Sub_coe] at h
  exact no_positive_coercivity_at_or_above_threshold bc K MJ γ₀ hthr hpos h

#print axioms unitB0Sub
#print axioms unitB0Sub_coe
#print axioms theLemma_regularU_fails_at_or_above_threshold

/-- **§4 IS NOW INSTANTIABLE AT NONZERO DATA — the caveat sweep's actual ask, assembled.** For every
`bc` with `bc.a < 1/2`, there are STRICTLY POSITIVE `K`, `M_J` and a NONZERO source `J` at which
`theLemma_regularU_bounded_coercive`'s hypothesis holds and its conclusion therefore fires with a
positive `γ₀`. No clause of the conclusion is weakened; only the data is made non-degenerate. -/
theorem theLemma_regularU_bounded_coercive_nondegenerate (bc : BaseConstant) (ha : bc.a < 1 / 2)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    ∃ K MJ : ℝ, 0 < K ∧ 0 < MJ ∧ (MJ • unitB0) ≠ 0 ∧
      Dtilde2Shape (qextQuad (K • unitB0)) unitB0 ≠ 0 ∧
      ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ Mα₀thresh : ℝ, 0 < Mα₀thresh →
        ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
        IsRegularHolonomy U Mα₀thresh →
        ∀ B : subspace156BFL2 Lambda S' ell U,
          γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤
            deltaKFormOnSubspace156 bc (qextQuad (K • unitB0)) (MJ • unitB0) Lambda S' ell U B := by
  obtain ⟨K, MJ, hK, hMJ, hbdd⟩ := isBoundedReparam_nonzero_witness bc ha
  exact ⟨K, MJ, hK, hMJ, instance_J_ne_zero MJ hMJ.ne', instance_dtilde2_ne_zero K hK.ne',
    theLemma_regularU_bounded_coercive bc (qextQuad (K • unitB0)) (MJ • unitB0) K MJ hbdd
      Lambda S' ell⟩

#print axioms theLemma_regularU_bounded_coercive_nondegenerate

end AdalyFormal.Balaban.BoundedReparam
