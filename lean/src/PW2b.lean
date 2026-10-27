import Mathlib

/-!
# PW2b -- abstract reduction R1q (quotient form): coercivity of `Φ + ‖R D*‖²` from two inputs on the
ORTHOGONAL COMPLEMENT of the gauge directions `D N` only:
  (Q) `cq ‖y‖² ≤ Φ y`, (I) `‖D* y‖² ≤ Ci Φ y`, for every `y` with `D* y ⟂ N`;
plus Poincaré on `N`, gauge invariance of `Φ` along `D N`, `R` a contraction fixing `D* D N`.
Sign hypotheses: `P ≥ 0`, `cq > 0`, `Ci ≥ 0`.
`‖x‖² ≤ (1/cq + 2P²(1+Ci)) (Φ x + ‖R D* x‖²)`.  No sorry / axiom.
-/
set_option autoImplicit false

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace

/-- the constant of R1q -/
noncomputable def Kq (cq Ci P : ℝ) : ℝ := 1 / cq + 2 * P ^ 2 * (1 + Ci)

section
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]

theorem r1q_coercive (D : S →L[ℝ] E) (N : Submodule ℝ S) (R : S →L[ℝ] S) (Φ : E → ℝ)
    (hΦinv : ∀ x, ∀ ν ∈ N, Φ (x + D ν) = Φ x)
    (hRfix : ∀ ν ∈ N, R (ContinuousLinearMap.adjoint D (D ν)) = ContinuousLinearMap.adjoint D (D ν))
    (hRc : ∀ s, ‖R s‖ ≤ ‖s‖)
    (P cq Ci : ℝ) (hP0 : 0 ≤ P) (hcq : 0 < cq) (hCi : 0 ≤ Ci)
    (hP : ∀ ν ∈ N, ‖ν‖ ≤ P * ‖D ν‖)
    (hQ : ∀ y, (∀ ν ∈ N, ⟪ContinuousLinearMap.adjoint D y, ν⟫ = 0) → cq * ‖y‖ ^ 2 ≤ Φ y)
    (hI : ∀ y, (∀ ν ∈ N, ⟪ContinuousLinearMap.adjoint D y, ν⟫ = 0) →
      ‖ContinuousLinearMap.adjoint D y‖ ^ 2 ≤ Ci * Φ y)
    (x : E) :
    ‖x‖ ^ 2 ≤ Kq cq Ci P * (Φ x + ‖R (ContinuousLinearMap.adjoint D x)‖ ^ 2) := by
  set Ds := ContinuousLinearMap.adjoint D with hDs
  set V : Submodule ℝ E := N.map (D : S →ₗ[ℝ] E) with hV
  haveI : FiniteDimensional ℝ V := inferInstance
  haveI : V.HasOrthogonalProjection := inferInstance
  set p : E := V.starProjection x with hp
  have hpV : p ∈ V := V.starProjection_apply_mem x
  obtain ⟨ν0, hν0N, hν0⟩ := Submodule.mem_map.mp hpV
  have hν0' : D ν0 = p := hν0
  set y : E := x - p with hy
  have hyperp : y ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
  have hxy : x = y + D ν0 := by rw [hν0', hy]; abel
  have hyorth : ∀ ν ∈ N, ⟪Ds y, ν⟫ = 0 := by
    intro ν hν
    rw [hDs, ContinuousLinearMap.adjoint_inner_left]
    have hm : D ν ∈ V := Submodule.mem_map.mpr ⟨ν, hν, rfl⟩
    have := (Submodule.mem_orthogonal V y).mp hyperp (D ν) hm
    rw [real_inner_comm]; exact this
  have hΦ : Φ x = Φ y := by rw [hxy, hΦinv y ν0 hν0N]
  have hIy := hI y hyorth
  have hQy := hQ y hyorth
  have hpy : ⟪y, D ν0⟫ = 0 := by
    have hm : D ν0 ∈ V := Submodule.mem_map.mpr ⟨ν0, hν0N, rfl⟩
    have := (Submodule.mem_orthogonal V y).mp hyperp (D ν0) hm
    rw [real_inner_comm]; exact this
  have hpyth : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖D ν0‖ ^ 2 := by
    rw [hxy, @norm_add_sq_real, hpy]; ring
  set Δν := Ds (D ν0) with hΔν
  have hRx : R (Ds x) = R (Ds y) + Δν := by
    rw [hxy, map_add, map_add, hRfix ν0 hν0N]
  have hΔle : ‖Δν‖ ≤ ‖R (Ds x)‖ + ‖Ds y‖ := by
    have : Δν = R (Ds x) - R (Ds y) := by rw [hRx]; abel
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hRc _))
  have hDν : ‖D ν0‖ ≤ P * ‖Δν‖ := by
    have h1 : ‖D ν0‖ ^ 2 = ⟪ν0, Δν⟫ := by
      rw [hΔν, hDs, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    have h2 : ⟪ν0, Δν⟫ ≤ ‖ν0‖ * ‖Δν‖ := real_inner_le_norm _ _
    have h3 : ‖ν0‖ * ‖Δν‖ ≤ P * ‖D ν0‖ * ‖Δν‖ :=
      mul_le_mul_of_nonneg_right (hP ν0 hν0N) (norm_nonneg _)
    rcases (norm_nonneg (D ν0)).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : ‖D ν0‖ * ‖D ν0‖ ≤ (P * ‖Δν‖) * ‖D ν0‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  set a := ‖R (Ds x)‖
  set b := ‖Ds y‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hΦy0 : 0 ≤ Φ y := le_trans (by positivity) hQy
  have hDν2 : ‖D ν0‖ ^ 2 ≤ 2 * P ^ 2 * (a ^ 2 + b ^ 2) := by
    have h1 : ‖D ν0‖ ≤ P * (a + b) := hDν.trans (mul_le_mul_of_nonneg_left hΔle hP0)
    have h2 : ‖D ν0‖ ^ 2 ≤ (P * (a + b)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (a - b), sq_nonneg P]
  have hy2 : ‖y‖ ^ 2 ≤ 1 / cq * Φ y := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hcq]; linarith
  unfold Kq
  rw [hpyth, hΦ]
  have hb2 : b ^ 2 ≤ Ci * Φ y := hIy
  have hk0 : 0 ≤ 1 / cq := by positivity
  nlinarith [mul_nonneg hk0 (sq_nonneg a), sq_nonneg P, mul_nonneg (sq_nonneg P) hΦy0,
    mul_nonneg (sq_nonneg P) (sq_nonneg a), mul_nonneg (mul_nonneg (sq_nonneg P) hCi) hΦy0]

end

#print axioms r1q_coercive

end AdalyFormal.M1Patch
