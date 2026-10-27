import DLR1

/-!
# DL9 -- abstract weighted (Combes–Thomas) toolkit

A WEIGHT on a real inner product space `X` is a pair `(w, w')` of self-adjoint CLMs with `w ∘ w' = id = w' ∘ w`.
For `T : X →L Z`: `T⁺ = ω_Z.w ∘ T ∘ ω_X.w'`, `T⁻ = ω_Z.w' ∘ T ∘ ω_X.w` (`cjp`, `cjm`).
* `cjp_comp` / `cjm_comp` (multiplicative), `adjoint_cjp` (`(T⁺)* = (T*)⁻`), `cjp_sub`, `cjp_add`, `cjp_smul`.
* `form_cjp_XtX` : `⟪f, (X*X)⁺ f⟫ = ⟪X⁻ f, X⁺ f⟫`.
* `xtx_cjp_lower` : `⟪f,(X*X)⁺f⟫ ≥ ½‖Xf‖² − 3δ²‖f‖²` when `‖X^± − X‖ ≤ δ`.
* `inv_cjp_bound` : if `M` is a unit, `M⁻¹` its inverse and `⟪h, M⁺h⟫ ≥ c‖h‖²`, then `c ‖(M⁻¹)⁺ g‖ ≤ ‖g‖`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

/-- a weight: mutually inverse self-adjoint operators -/
structure WPair (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  w : X →L[ℝ] X
  wi : X →L[ℝ] X
  w_wi : ∀ x, w (wi x) = x
  wi_w : ∀ x, wi (w x) = x
  w_sym : ∀ x y, ⟪w x, y⟫ = ⟪x, w y⟫
  wi_sym : ∀ x y, ⟪wi x, y⟫ = ⟪x, wi y⟫

section
variable {X Y Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- the inverse weight -/
def WPair.inv (ω : WPair X) : WPair X where
  w := ω.wi
  wi := ω.w
  w_wi := ω.wi_w
  wi_w := ω.w_wi
  w_sym := ω.wi_sym
  wi_sym := ω.w_sym

/-- `T⁺ = ω_Z T ω_X⁻¹` -/
noncomputable def cjp (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) : X →L[ℝ] Z := ωZ.w ∘L T ∘L ωX.wi

/-- `T⁻ = ω_Z⁻¹ T ω_X` -/
noncomputable def cjm (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) : X →L[ℝ] Z := ωZ.wi ∘L T ∘L ωX.w

theorem cjm_eq_cjp_inv (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) : cjm ωX ωZ T = cjp ωX.inv ωZ.inv T := rfl

theorem cjp_apply (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) (x : X) : cjp ωX ωZ T x = ωZ.w (T (ωX.wi x)) := rfl

theorem cjp_comp (ωX : WPair X) (ωY : WPair Y) (ωZ : WPair Z) (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y) :
    cjp ωX ωZ (S ∘L T) = cjp ωY ωZ S ∘L cjp ωX ωY T := by
  ext x; simp [cjp, ωY.wi_w]

theorem cjm_comp (ωX : WPair X) (ωY : WPair Y) (ωZ : WPair Z) (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y) :
    cjm ωX ωZ (S ∘L T) = cjm ωY ωZ S ∘L cjm ωX ωY T := by
  ext x; simp [cjm, ωY.w_wi]

theorem cjp_sub (ωX : WPair X) (ωZ : WPair Z) (S T : X →L[ℝ] Z) :
    cjp ωX ωZ (S - T) = cjp ωX ωZ S - cjp ωX ωZ T := by
  ext x; simp [cjp]

theorem cjp_add (ωX : WPair X) (ωZ : WPair Z) (S T : X →L[ℝ] Z) :
    cjp ωX ωZ (S + T) = cjp ωX ωZ S + cjp ωX ωZ T := by
  ext x; simp [cjp]

theorem cjp_smul (ωX : WPair X) (ωZ : WPair Z) (c : ℝ) (T : X →L[ℝ] Z) :
    cjp ωX ωZ (c • T) = c • cjp ωX ωZ T := by
  ext x; simp [cjp]

theorem cjp_id (ωX : WPair X) : cjp ωX ωX (ContinuousLinearMap.id ℝ X) = ContinuousLinearMap.id ℝ X := by
  ext x; simp [cjp, ωX.w_wi]

variable [CompleteSpace X] [CompleteSpace Z]

/-- `(T⁺)* = (T*)⁻` -/
theorem adjoint_cjp (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) :
    ContinuousLinearMap.adjoint (cjp ωX ωZ T) = cjm ωZ ωX (ContinuousLinearMap.adjoint T) := by
  refine ContinuousLinearMap.ext (fun z => ext_inner_left ℝ (fun x => ?_))
  rw [ContinuousLinearMap.adjoint_inner_right, cjp_apply, cjm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← ωX.wi_sym, ContinuousLinearMap.adjoint_inner_right, ωZ.w_sym]

theorem adjoint_cjm (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) :
    ContinuousLinearMap.adjoint (cjm ωX ωZ T) = cjp ωZ ωX (ContinuousLinearMap.adjoint T) := by
  rw [cjm_eq_cjp_inv, adjoint_cjp]; rfl

/-- `⟪f, (X*X)⁺ f⟫ = ⟪X⁻f, X⁺f⟫` -/
theorem form_cjp_XtX (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) (f : X) :
    ⟪f, cjp ωX ωX (ContinuousLinearMap.adjoint T ∘L T) f⟫ = ⟪cjm ωX ωZ T f, cjp ωX ωZ T f⟫ := by
  rw [cjp_comp ωX ωZ ωX, ← adjoint_cjm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- `⟪f,(X*X)⁺f⟫ ≥ ½‖Xf‖² − 3δ²‖f‖²` -/
theorem xtx_cjp_lower (ωX : WPair X) (ωZ : WPair Z) (T : X →L[ℝ] Z) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ‖cjp ωX ωZ T - T‖ ≤ δ) (hm : ‖cjm ωX ωZ T - T‖ ≤ δ) (f : X) :
    (1 / 2) * ‖T f‖ ^ 2 - 3 * δ ^ 2 * ‖f‖ ^ 2 ≤ ⟪f, cjp ωX ωX (ContinuousLinearMap.adjoint T ∘L T) f⟫ := by
  rw [form_cjp_XtX ωX ωZ]
  have hpl := pair_lower (T f) (cjp ωX ωZ T f) (cjm ωX ωZ T f)
  have e1 : ‖cjp ωX ωZ T f - T f‖ ≤ δ * ‖f‖ := by
    have := (cjp ωX ωZ T - T).le_opNorm f
    rw [ContinuousLinearMap.sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have e2 : ‖cjm ωX ωZ T f - T f‖ ≤ δ * ‖f‖ := by
    have := (cjm ωX ωZ T - T).le_opNorm f
    rw [ContinuousLinearMap.sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _))
  have hdf : 0 ≤ δ * ‖f‖ := by positivity
  have h1 : ‖T f‖ * (‖cjp ωX ωZ T f - T f‖ + ‖cjm ωX ωZ T f - T f‖) ≤ ‖T f‖ * (2 * (δ * ‖f‖)) := by
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
  have h2 : ‖cjp ωX ωZ T f - T f‖ * ‖cjm ωX ωZ T f - T f‖ ≤ (δ * ‖f‖) * (δ * ‖f‖) :=
    mul_le_mul e1 e2 (norm_nonneg _) hdf
  nlinarith [sq_nonneg (‖T f‖ - 2 * (δ * ‖f‖)), norm_nonneg (T f)]

/-- the CT inverse step: `c ‖(M⁻¹)⁺ g‖ ≤ ‖g‖` -/
theorem inv_cjp_bound (ωX : WPair X) (M Minv : X →L[ℝ] X) (hinv : ∀ x, M (Minv x) = x)
    (c : ℝ) (hco : ∀ h, c * ‖h‖ ^ 2 ≤ ⟪h, cjp ωX ωX M h⟫) (g : X) :
    c * ‖cjp ωX ωX Minv g‖ ≤ ‖g‖ := by
  set h := cjp ωX ωX Minv g with hh
  have hM : cjp ωX ωX M h = g := by
    rw [hh, cjp_apply, cjp_apply, ωX.wi_w, hinv, ωX.w_wi]
  have h1 := hco h
  rw [hM] at h1
  have h2 : ⟪h, g⟫ ≤ ‖h‖ * ‖g‖ := real_inner_le_norm h g
  by_cases h0 : ‖h‖ = 0
  · rw [h0, mul_zero]; exact norm_nonneg _
  have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have : c * ‖h‖ * ‖h‖ ≤ ‖g‖ * ‖h‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

end

#print axioms WPair.inv
#print axioms cjp
#print axioms cjm
#print axioms cjp_comp
#print axioms cjm_comp
#print axioms cjp_sub
#print axioms cjp_add
#print axioms cjp_smul
#print axioms cjp_id
#print axioms adjoint_cjp
#print axioms adjoint_cjm
#print axioms form_cjp_XtX
#print axioms xtx_cjp_lower
#print axioms inv_cjp_bound

end AdalyFormal.DLayer
