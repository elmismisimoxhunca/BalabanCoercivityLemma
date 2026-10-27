import DG1

/-!
# DY4a -- a split form perturbed by a small symmetric operator is again a split form (abstract)
(M1 D-layer lane, clause 2, 2026-10-14)

`J : GSplit`, `Dl` symmetric-free (only its bilinear form is used), an auxiliary size `n ≥ ‖Nw ·‖` with `cw₀ n² ≤ E`
(the W4 form), `|⟪x, Dl y⟫| ≤ δ₀ n(x) n(y)` and `|⟪ωE x, Dl ωE⁻¹ y⟫| ≤ δ₁ n(x) n(y)`, `δ₀ < cw₀`.
* **`GSplit.pert`** : the split of `Ginv − Dl` with `cw = cw₀ − δ₀`, `cΔ = λ² cΔ + δ₀/(cw₀−δ₀)`,
  `cΔ' = λ² cΔ' + δ₁/(cw₀−δ₀)`, `λ² = cw₀/(cw₀−δ₀)`, the same squares and the same conjugation errors.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.DLayer

namespace GSplit

variable {E F1 F2 F3 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F1] [InnerProductSpace ℝ F1] [NormedAddCommGroup F2] [InnerProductSpace ℝ F2]
  [NormedAddCommGroup F3] [InnerProductSpace ℝ F3]
variable (J : GSplit E F1 F2 F3) (Dl : E →L[ℝ] E) (n : E → ℝ) (cw0 δ0 δ1 : ℝ)
  (hn0 : ∀ x, 0 ≤ n x) (hNn : ∀ x, ‖J.Nw x‖ ≤ n x) (hW : ∀ x, cw0 * n x ^ 2 ≤ ⟪x, J.Ginv x⟫)
  (hD0 : ∀ x y, |⟪x, Dl y⟫| ≤ δ0 * (n x * n y))
  (hδ0 : 0 ≤ δ0) (hlt : δ0 < cw0)

include hn0 hW hD0 hδ0 hlt in
theorem pert_lower (x : E) : (cw0 - δ0) * n x ^ 2 ≤ ⟪x, (J.Ginv - Dl) x⟫ := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  have h1 := hW x
  have h2 := hD0 x x
  have h3 : ⟪x, Dl x⟫ ≤ δ0 * (n x * n x) := (le_abs_self _).trans h2
  nlinarith

include hn0 hW hD0 hδ0 hlt in
theorem pert_E_le (x : E) : ⟪x, J.Ginv x⟫ ≤ cw0 / (cw0 - δ0) * ⟪x, (J.Ginv - Dl) x⟫ := by
  have hc : 0 < cw0 - δ0 := by linarith
  have hc0 : 0 < cw0 := by linarith
  have h1 := hW x
  have h2 := hD0 x x
  have h3 : ⟪x, Dl x⟫ ≤ δ0 * (n x * n x) := (le_abs_self _).trans h2
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, div_mul_eq_mul_div, le_div_iff₀ hc]
  -- `E (cw₀ − δ₀) ≤ cw₀ (E − ⟪x,Dl x⟫)` ⟸ `cw₀ ⟪x,Dl x⟫ ≤ δ₀ E` ⟸ `cw₀ δ₀ n² ≤ δ₀ E`
  have h4 : cw0 * ⟪x, Dl x⟫ ≤ δ0 * ⟪x, J.Ginv x⟫ := by
    have := mul_le_mul_of_nonneg_left h1 hδ0
    have h5 : cw0 * ⟪x, Dl x⟫ ≤ cw0 * (δ0 * (n x * n x)) := mul_le_mul_of_nonneg_left h3 hc0.le
    nlinarith
  nlinarith

include hn0 hW hD0 hδ0 hlt in
theorem pert_sqrtE (x : E) :
    Real.sqrt ⟪x, J.Ginv x⟫ ≤ Real.sqrt (cw0 / (cw0 - δ0)) * Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ := by
  rw [← Real.sqrt_mul (by have : 0 < cw0 - δ0 := by linarith
                          have : 0 < cw0 := by linarith
                          positivity)]
  exact Real.sqrt_le_sqrt (pert_E_le J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x)

include hn0 hW hD0 hδ0 hlt in
theorem pert_n (x : E) : n x ≤ Real.sqrt (1 / (cw0 - δ0)) * Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ := by
  have hc : 0 < cw0 - δ0 := by linarith
  have h := pert_lower J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq (hn0 x)]
  apply Real.sqrt_le_sqrt
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  linarith

include hn0 hW hD0 hδ0 hlt in
theorem pert_EE (x y : E) :
    Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪y, J.Ginv y⟫
      ≤ cw0 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) := by
  have hc : 0 < cw0 - δ0 := by linarith
  have hc0 : 0 < cw0 := by linarith
  have h1 := pert_sqrtE J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x
  have h2 := pert_sqrtE J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt y
  have hs : Real.sqrt (cw0 / (cw0 - δ0)) * Real.sqrt (cw0 / (cw0 - δ0)) = cw0 / (cw0 - δ0) :=
    Real.mul_self_sqrt (by positivity)
  calc Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪y, J.Ginv y⟫
      ≤ (Real.sqrt (cw0 / (cw0 - δ0)) * Real.sqrt ⟪x, (J.Ginv - Dl) x⟫)
        * (Real.sqrt (cw0 / (cw0 - δ0)) * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt (cw0 / (cw0 - δ0)) * Real.sqrt (cw0 / (cw0 - δ0)))
        * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) := by ring
    _ = _ := by rw [hs]

include hn0 hW hD0 hδ0 hlt in
theorem pert_nn (x y : E) :
    n x * n y ≤ 1 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) := by
  have hc : 0 < cw0 - δ0 := by linarith
  have h1 := pert_n J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x
  have h2 := pert_n J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt y
  have hs : Real.sqrt (1 / (cw0 - δ0)) * Real.sqrt (1 / (cw0 - δ0)) = 1 / (cw0 - δ0) :=
    Real.mul_self_sqrt (by positivity)
  calc n x * n y ≤ (Real.sqrt (1 / (cw0 - δ0)) * Real.sqrt ⟪x, (J.Ginv - Dl) x⟫)
        * (Real.sqrt (1 / (cw0 - δ0)) * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) :=
        mul_le_mul h1 h2 (hn0 y) (by positivity)
    _ = (Real.sqrt (1 / (cw0 - δ0)) * Real.sqrt (1 / (cw0 - δ0)))
        * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫) := by ring
    _ = _ := by rw [hs]

/-- **the perturbed split** -/
noncomputable def pert (hD1 : ∀ x y, |⟪J.ωE.w x, Dl (J.ωE.wi y)⟫| ≤ δ1 * (n x * n y)) (hδ1 : 0 ≤ δ1) :
    GSplit E F1 F2 F3 where
  Ginv := J.Ginv - Dl
  Nw := J.Nw
  ωE := J.ωE
  Y1 := J.Y1
  Y2 := J.Y2
  Y3 := J.Y3
  ω1 := J.ω1
  ω2 := J.ω2
  ω3 := J.ω3
  Δ := fun x y => J.Δ x y - ⟪x, Dl y⟫
  cw := cw0 - δ0
  cΔ := cw0 / (cw0 - δ0) * J.cΔ + δ0 / (cw0 - δ0)
  cΔ' := cw0 / (cw0 - δ0) * J.cΔ' + δ1 / (cw0 - δ0)
  d1 := J.d1
  d2 := J.d2
  d3 := J.d3
  hcw := by linarith
  hcΔ := by
    have : 0 < cw0 - δ0 := by linarith
    have : 0 < cw0 := by linarith
    have := J.hcΔ
    positivity
  hcΔ' := by
    have : 0 < cw0 - δ0 := by linarith
    have : 0 < cw0 := by linarith
    have := J.hcΔ'
    positivity
  hd1 := J.hd1
  hd2 := J.hd2
  hd3 := J.hd3
  hdec := fun x y => by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, J.hdec]; ring
  hcoer := fun f => by
    have hc : 0 ≤ cw0 - δ0 := by linarith
    have h1 := pert_lower J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt f
    have h2 : ‖J.Nw f‖ ^ 2 ≤ n f ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hNn f) 2
    have := mul_le_mul_of_nonneg_left h2 hc
    linarith
  hΔ0 := fun x y => by
    have hc : 0 < cw0 - δ0 := by linarith
    have hc0 : 0 < cw0 := by linarith
    have h1 := J.hΔ0 x y
    have h2 := hD0 x y
    have h3 := pert_EE J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x y
    have h4 := pert_nn J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x y
    have hs : 0 ≤ Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫ := by positivity
    have h5 : J.cΔ * (Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪y, J.Ginv y⟫)
        ≤ J.cΔ * (cw0 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) :=
      mul_le_mul_of_nonneg_left h3 J.hcΔ
    have h6 : δ0 * (n x * n y)
        ≤ δ0 * (1 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) :=
      mul_le_mul_of_nonneg_left h4 hδ0
    calc |J.Δ x y - ⟪x, Dl y⟫| ≤ |J.Δ x y| + |⟪x, Dl y⟫| := abs_sub _ _
      _ ≤ _ := by
        have e : (cw0 / (cw0 - δ0) * J.cΔ + δ0 / (cw0 - δ0))
            * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)
            = J.cΔ * (cw0 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫))
              + δ0 * (1 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) := by
          field_simp
        rw [e]; linarith
  hΔ1 := fun x y => by
    have hc : 0 < cw0 - δ0 := by linarith
    have hc0 : 0 < cw0 := by linarith
    have h1 := J.hΔ1 x y
    have h2 := hD1 x y
    have h3 := pert_EE J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x y
    have h4 := pert_nn J Dl n cw0 δ0 hn0 hW hD0 hδ0 hlt x y
    have h5 : J.cΔ' * (Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪y, J.Ginv y⟫)
        ≤ J.cΔ' * (cw0 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) :=
      mul_le_mul_of_nonneg_left h3 J.hcΔ'
    have h6 : δ1 * (n x * n y)
        ≤ δ1 * (1 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) :=
      mul_le_mul_of_nonneg_left h4 hδ1
    calc |J.Δ (J.ωE.w x) (J.ωE.wi y) - ⟪J.ωE.w x, Dl (J.ωE.wi y)⟫|
        ≤ |J.Δ (J.ωE.w x) (J.ωE.wi y)| + |⟪J.ωE.w x, Dl (J.ωE.wi y)⟫| := abs_sub _ _
      _ ≤ _ := by
        have e : (cw0 / (cw0 - δ0) * J.cΔ' + δ1 / (cw0 - δ0))
            * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)
            = J.cΔ' * (cw0 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫))
              + δ1 * (1 / (cw0 - δ0) * (Real.sqrt ⟪x, (J.Ginv - Dl) x⟫ * Real.sqrt ⟪y, (J.Ginv - Dl) y⟫)) := by
          field_simp
        rw [e]; linarith
  hp1 := J.hp1
  hm1 := J.hm1
  hp2 := J.hp2
  hm2 := J.hm2
  hp3 := J.hp3
  hm3 := J.hm3

end GSplit

#print axioms GSplit.pert_lower
#print axioms GSplit.pert_E_le
#print axioms GSplit.pert_sqrtE
#print axioms GSplit.pert_n
#print axioms GSplit.pert_EE
#print axioms GSplit.pert_nn
#print axioms GSplit.pert

end AdalyFormal.M1DStrat
