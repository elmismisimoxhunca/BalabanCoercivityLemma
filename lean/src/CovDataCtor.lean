/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.VariationalProjectorH1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `BalabanCovarianceData` BUILT from `(Ginv` positive definite`, Q` surjective`)`

`compute/hbase_plumbing/SCOPE.md` §6 records this as **fully designed and not built — budget**, and
says plainly it is "mechanically closable … unfinished work, not a residual".  It is built here.

`AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData` carries `Gstar`, `Comp`,
`CompInv` and their four inverse laws as STRUCTURE FIELDS, i.e. as assumptions.  Every one of them
is discharged below from two hypotheses that are checkable at the lattice:

* `Ginv` self-adjoint and **positive definite** (`0 < ⟨x, Ginv x⟩` for `x ≠ 0`);
* `Q` **surjective**.

Finite-dimensionality of both carriers is used (injective ⟹ bijective); Bałaban's spaces are
finite lattices, and `hbase_plumbing`'s own `Assembly` already carries `FiniteDimensional`.

## Why surjectivity of `Q` is exactly the right hypothesis

`compute/hbase_plumbing/HBase.lean`'s banner records a precision gap in CMP96 p.225: the page
concludes "`G'²` and `Q'G'²Q'*` are positive operators, hence `(Q'G'²Q'*)⁻¹` is well defined",
but `Q'G'²Q'*` is positive DEFINITE only if `Q'*` is injective, i.e. only if `Q'` is surjective.
This module makes that precise in both directions:

* `comp_posDef` and `build` (§2) prove the inverse exists when `Q` is surjective;
* `comp_not_injective_of_adjoint_kernel` (§3) proves that when `Q*` has a non-zero kernel vector
  the operator `Comp = QG_starQ*` kills it, so no `CompInv` field can be filled at all.

So the hypothesis is not a convenience: it is necessary and sufficient (given `Gstar` positive
definite) for the structure to be inhabitable.

Nothing here is graded by this lane (BUILD DISCIPLINE 8).
-/

namespace AdalyFormal.HBaseInputs.CovData

open scoped InnerProductSpace
open AdalyFormal.Balaban.VariationalProjectorH1

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-! ## §1. Inverting a positive definite self-adjoint operator -/

/-- A positive definite operator is injective, hence (finite dimensions) bijective. -/
theorem bijective_of_posDef (S : H →L[ℝ] H)
    (hpd : ∀ x : H, x ≠ 0 → (0 : ℝ) < inner ℝ x (S x)) : Function.Bijective S := by
  have hinj : Function.Injective S := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.2 hne
    have hz : S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hpd _ hsub
    rw [hz, inner_zero_right] at this
    exact lt_irrefl _ this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (S : H →ₗ[ℝ] H))).1 hinj⟩

/-- The two-sided inverse of a bijective continuous linear map on a finite-dimensional space,
as a continuous linear map. -/
noncomputable def invOf (S : H →L[ℝ] H) (hbij : Function.Bijective S) : H →L[ℝ] H :=
  LinearMap.toContinuousLinearMap
    (LinearEquiv.ofBijective (S : H →ₗ[ℝ] H) hbij).symm.toLinearMap

theorem invOf_right (S : H →L[ℝ] H) (hbij : Function.Bijective S) (x : H) :
    S (invOf S hbij x) = x :=
  (LinearEquiv.ofBijective (S : H →ₗ[ℝ] H) hbij).apply_symm_apply x

theorem invOf_left (S : H →L[ℝ] H) (hbij : Function.Bijective S) (x : H) :
    invOf S hbij (S x) = x :=
  (LinearEquiv.ofBijective (S : H →ₗ[ℝ] H) hbij).symm_apply_apply x

/-- **The inverse of a positive definite self-adjoint operator is again positive definite.**  This
is the step that turns `Ginv > 0` into `Gstar > 0`, which is what makes `QG_starQ*` positive. -/
theorem invOf_posDef (S : H →L[ℝ] H)
    (hpd : ∀ x : H, x ≠ 0 → (0 : ℝ) < inner ℝ x (S x))
    (hbij : Function.Bijective S) (u : H) (hu : u ≠ 0) :
    (0 : ℝ) < inner ℝ u (invOf S hbij u) := by
  set v := invOf S hbij u with hv
  have hSv : S v = u := invOf_right S hbij u
  have hvne : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hSv
    exact hu hSv.symm
  have heq : (inner ℝ u v : ℝ) = inner ℝ v (S v) := by
    rw [← hSv]
    exact real_inner_comm v (S v)
  rw [heq]
  exact hpd v hvne

/-! ## §2. THE CONSTRUCTOR -/

section Build

variable (Ginv : H →L[ℝ] H) (Q : H →L[ℝ] K)
  (hsa : ∀ x y : H, (inner ℝ (Ginv x) y : ℝ) = inner ℝ x (Ginv y))
  (hpd : ∀ x : H, x ≠ 0 → (0 : ℝ) < inner ℝ x (Ginv x))
  (hsurj : Function.Surjective Q)

include hpd in
theorem ginv_bijective : Function.Bijective Ginv := bijective_of_posDef Ginv hpd

include hsurj in
/-- `Q*` is injective exactly because `Q` is surjective — the step CMP96 p.225 leaves implicit. -/
theorem adjoint_injective (y : K) (hy : ContinuousLinearMap.adjoint Q y = 0) : y = 0 := by
  have hall : ∀ z : K, (inner ℝ z y : ℝ) = 0 := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    rw [← hx, ← ContinuousLinearMap.adjoint_inner_right, hy, inner_zero_right]
  have := hall y
  rw [real_inner_self_eq_norm_sq] at this
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp this

include hpd hsurj in
/-- `Comp = QG_starQ*` is positive definite. -/
theorem comp_posDef (y : K) (hy : y ≠ 0) :
    (0 : ℝ) < inner ℝ y (Q (invOf Ginv (ginv_bijective Ginv hpd)
      (ContinuousLinearMap.adjoint Q y))) := by
  set Gstar := invOf Ginv (ginv_bijective Ginv hpd) with hG
  set w := ContinuousLinearMap.adjoint Q y with hw
  have hwne : w ≠ 0 := fun h => hy (adjoint_injective Q hsurj y h)
  have h1 : (inner ℝ (Gstar w) w : ℝ) = inner ℝ (Q (Gstar w)) y := by
    rw [hw]; exact ContinuousLinearMap.adjoint_inner_right Q (Gstar w) y
  have hmove : (inner ℝ y (Q (Gstar w)) : ℝ) = inner ℝ w (Gstar w) :=
    calc (inner ℝ y (Q (Gstar w)) : ℝ) = inner ℝ (Q (Gstar w)) y := real_inner_comm _ _
      _ = inner ℝ (Gstar w) w := h1.symm
      _ = inner ℝ w (Gstar w) := real_inner_comm _ _
  rw [hmove]
  exact invOf_posDef Ginv hpd (ginv_bijective Ginv hpd) w hwne

include hsa hpd hsurj in
/-- **THE CONSTRUCTOR.**  Every field of `BalabanCovarianceData` discharged from
`(Ginv` self-adjoint positive definite`, Q` surjective`)`. -/
noncomputable def build : BalabanCovarianceData H K where
  Ginv := Ginv
  Gstar := invOf Ginv (ginv_bijective Ginv hpd)
  Ginv_Gstar := invOf_right Ginv (ginv_bijective Ginv hpd)
  Gstar_Ginv := invOf_left Ginv (ginv_bijective Ginv hpd)
  Ginv_selfAdjoint := hsa
  Ginv_posSemidef := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact le_of_lt (hpd x hx)
  Q := Q
  Qstar := ContinuousLinearMap.adjoint Q
  Q_Qstar_adjoint := fun x y => (ContinuousLinearMap.adjoint_inner_right Q x y).symm
  Comp := Q.comp ((invOf Ginv (ginv_bijective Ginv hpd)).comp (ContinuousLinearMap.adjoint Q))
  Comp_eq := fun _ => rfl
  CompInv := invOf
    (Q.comp ((invOf Ginv (ginv_bijective Ginv hpd)).comp (ContinuousLinearMap.adjoint Q)))
    (bijective_of_posDef _ (fun y hy => comp_posDef Ginv Q hpd hsurj y hy))
  Comp_CompInv := invOf_right _ _
  CompInv_Comp := invOf_left _ _

include hsa hpd hsurj in
@[simp] theorem build_Q : (build Ginv Q hsa hpd hsurj).Q = Q := rfl

include hsa hpd hsurj in
@[simp] theorem build_Ginv : (build Ginv Q hsa hpd hsurj).Ginv = Ginv := rfl

include hsa hpd hsurj in
/-- The interpolation property `Q(H_starB) = B` now holds with NO undischarged field. -/
theorem build_interpolates (B : K) :
    (build Ginv Q hsa hpd hsurj).Q
        (solutionOperator (build Ginv Q hsa hpd hsurj) B) = B :=
  interpolates _ B

end Build

/-! ## §3. THE GUARDS — the hypotheses are not decoration -/

/-- **MUST-FIRE (necessity of surjectivity).**  If `Q` is not surjective, `Q*` has a non-zero
kernel vector `y`, and then `Comp y = QG_starQ*y = 0`, so the `CompInv_Comp` field is
unfillable — no `BalabanCovarianceData` with this `Q` and any `Gstar` exists.  Stated in the
general form so it is not an artefact of one example. -/
theorem comp_not_injective_of_adjoint_kernel (Gstar : H →L[ℝ] H) (Q : H →L[ℝ] K) (y : K)
    (hy : y ≠ 0) (hker : ContinuousLinearMap.adjoint Q y = 0) :
    Q (Gstar (ContinuousLinearMap.adjoint Q y)) = 0 ∧ y ≠ 0 := by
  refine ⟨?_, hy⟩
  rw [hker, map_zero, map_zero]

/-- A concrete `Q` that is not surjective, with the kernel vector exhibited: `Q = 0 : ℝ →L ℝ`.
Then `Comp = 0` and `Comp 1 = 0 ≠ 1`, so `Comp` is not injective and `CompInv_Comp` fails. -/
theorem zero_map_not_surjective : ¬ Function.Surjective (0 : ℝ →L[ℝ] ℝ) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  simp at hx

theorem zero_map_comp_kernel :
    ((0 : ℝ →L[ℝ] ℝ) ((ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ) (1 : ℝ)))) = 0 ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨by simp, one_ne_zero⟩

/-! ### §3b. MUST-NOT-FIRE: the constructor produces a NON-DEGENERATE object -/

/-- `Ginv = id` on `ℝ` is self-adjoint and positive definite. -/
theorem id_selfAdjoint : ∀ x y : ℝ, (inner ℝ ((ContinuousLinearMap.id ℝ ℝ) x) y : ℝ)
    = inner ℝ x ((ContinuousLinearMap.id ℝ ℝ) y) := fun _ _ => rfl

theorem id_posDef : ∀ x : ℝ, x ≠ 0 → (0 : ℝ) < inner ℝ x ((ContinuousLinearMap.id ℝ ℝ) x) := by
  intro x hx
  simp only [ContinuousLinearMap.id_apply]
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hx) 2

theorem id_surjective : Function.Surjective (ContinuousLinearMap.id ℝ ℝ) := fun y => ⟨y, rfl⟩

/-- **The built structure is not vacuous**: on `H = K = ℝ` with `Ginv = Q = id`, the solution
operator is the identity, so `H_star 1 = 1 ≠ 0`.  Without this, §2 could be satisfied by data on a
trivial space where every field is `0`. -/
theorem build_nondegenerate :
    solutionOperator
        (build (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
          id_selfAdjoint id_posDef id_surjective) (1 : ℝ) ≠ 0 := by
  have h : (build (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
      id_selfAdjoint id_posDef id_surjective).Q
        (solutionOperator (build (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
          id_selfAdjoint id_posDef id_surjective) (1 : ℝ)) = 1 :=
    build_interpolates _ _ id_selfAdjoint id_posDef id_surjective 1
  intro hzero
  rw [hzero, map_zero] at h
  exact one_ne_zero h.symm

end AdalyFormal.HBaseInputs.CovData
