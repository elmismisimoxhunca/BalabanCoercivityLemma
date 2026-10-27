import DLR16

/-!
# DL17 -- the `G⁻¹` Combes–Thomas inequality (abstract) and the weighted bound of `G`

* `EA2`, `EG` (explicit error constants); `Ginv_CT` : `⟪f,(G⁻¹)⁺f⟫ ≥ ¾⟪f,G⁻¹f⟫ − E_G‖f‖²`.
* `G_cjp_le` : if `G⁻¹` has a two-sided inverse `Gi`, `cg‖f‖² ≤ ⟪f,G⁻¹f⟫` and `4E_G ≤ cg`, then `(cg/2)‖Gi⁺ g‖ ≤ ‖g‖`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace GinvHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (I : GinvHyp S E Y P B)

noncomputable def EA2 : ℝ :=
  I.nW * I.ν * I.Gm.dW + I.nW * I.δν * (I.nW + I.Gm.dW) + I.Gm.dW * (I.ν + I.δν) * (I.nW + I.Gm.dW)

noncomputable def EG : ℝ :=
  (1 / 4) * I.ν * I.nW ^ 2 + 5 * I.δCW ^ 2 + 5 * I.Gm.dT ^ 2 + 5 * I.M * I.δB ^ 2 + I.EA2

theorem cjpGinv_form (f : E) : ⟪f, cjp I.ωE I.ωE I.Ginv f⟫
    = ⟪cjm I.ωE I.ωP (I.C ∘L I.Gm.W) f, cjp I.ωE I.ωP (I.C ∘L I.Gm.W) f⟫
      + ⟪cjm I.ωE I.ωE I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫
      + ⟪cjm I.ωE I.ωS I.Gm.T f, cjp I.ωE I.ωS I.Gm.T f⟫
      + I.M * ⟪cjm I.ωE I.ωB I.Qb f, cjp I.ωE I.ωB I.Qb f⟫ := by
  have e1 : cjp I.ωE I.ωE I.Ginv
      = ContinuousLinearMap.adjoint (cjm I.ωE I.ωP (I.C ∘L I.Gm.W)) ∘L cjp I.ωE I.ωP (I.C ∘L I.Gm.W)
        + ContinuousLinearMap.adjoint (cjm I.ωE I.ωE I.Gm.W) ∘L cjp I.ωE I.ωE I.Dp ∘L cjp I.ωE I.ωE I.Gm.W
        + ContinuousLinearMap.adjoint (cjm I.ωE I.ωS I.Gm.T) ∘L cjp I.ωE I.ωS I.Gm.T
        + I.M • (ContinuousLinearMap.adjoint (cjm I.ωE I.ωB I.Qb) ∘L cjp I.ωE I.ωB I.Qb) := by
    have hsplit : I.Ginv = ContinuousLinearMap.adjoint (I.C ∘L I.Gm.W) ∘L (I.C ∘L I.Gm.W)
        + ContinuousLinearMap.adjoint I.Gm.W ∘L I.Dp ∘L I.Gm.W
        + ContinuousLinearMap.adjoint I.Gm.T ∘L I.Gm.T + I.M • (ContinuousLinearMap.adjoint I.Qb ∘L I.Qb) := by
      ext v
      simp only [Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.adjoint_comp, map_add]
    rw [hsplit, cjp_add, cjp_add, cjp_add, cjp_smul, cjp_comp I.ωE I.ωP I.ωE, cjp_comp I.ωE I.ωE I.ωE,
      cjp_comp I.ωE I.ωE I.ωE, cjp_comp I.ωE I.ωS I.ωE, cjp_comp I.ωE I.ωB I.ωE,
      adjoint_cjm, adjoint_cjm, adjoint_cjm, adjoint_cjm]
  rw [e1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]

theorem pair_aux {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u up um : V) (d : ℝ) (hd : 0 ≤ d)
    (r : ℝ) (hp : ‖up - u‖ ≤ d * r) (hm : ‖um - u‖ ≤ d * r) (hr : 0 ≤ r) :
    ‖u‖ ^ 2 - 2 * ‖u‖ * (d * r) - (d * r) ^ 2 ≤ ⟪um, up⟫ := by
  have h := pair_lower u up um
  have h1 : ‖u‖ * (‖up - u‖ + ‖um - u‖) ≤ ‖u‖ * (2 * (d * r)) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have h2 : ‖up - u‖ * ‖um - u‖ ≤ (d * r) * (d * r) := mul_le_mul hp hm (norm_nonneg _) (by positivity)
  nlinarith

theorem dZ_nonneg : 0 ≤ I.Gm.dZ ∧ 0 ≤ I.Gm.dDZ ∧ 0 ≤ I.Gm.kZ ∧ 0 ≤ I.Gm.kDZ ∧ 0 ≤ I.Gm.dW ∧ 0 ≤ I.Gm.dT := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := I.Gm.consts_nonneg
  have hc := I.hc; have hq := I.hq; have hδD := I.hδD
  have hK0 := I.Gm.H.K0_nonneg I.q I.hq
  have hK1 := I.Gm.H.K1_nonneg I.q I.hq
  have he := I.Gm.H.epsX_nonneg I.q I.hq
  have hdZ : 0 ≤ I.Gm.dZ := by unfold GamHyp.dZ; positivity
  have hdDZ : 0 ≤ I.Gm.dDZ := by unfold GamHyp.dDZ; positivity
  have hkZ : 0 ≤ I.Gm.kZ := by unfold GamHyp.kZ; positivity
  have hkDZ : 0 ≤ I.Gm.kDZ := by unfold GamHyp.kDZ; positivity
  refine ⟨hdZ, hdDZ, hkZ, hkDZ, by unfold GamHyp.dW; positivity, by unfold GamHyp.dT; positivity⟩

theorem Ginv_CT (f : E) : (3 / 4) * ⟪f, I.Ginv f⟫ - I.EG * ‖f‖ ^ 2 ≤ ⟪f, cjp I.ωE I.ωE I.Ginv f⟫ := by
  rw [cjpGinv_form, Ginv_form]
  have hf0 := norm_nonneg f
  obtain ⟨hdZ, hdDZ, hkZ, hkDZ, hdW, hdT⟩ := I.dZ_nonneg
  have hδCW : 0 ≤ I.δCW := by
    unfold δCW; have := I.hδC; have := I.hδK; have := I.hκ; positivity
  have hnW : 0 ≤ I.nW := by unfold nW; linarith
  -- CW term
  have A1 : ‖I.C (I.Gm.W f)‖ ^ 2 - 2 * ‖I.C (I.Gm.W f)‖ * (I.δCW * ‖f‖) - (I.δCW * ‖f‖) ^ 2
      ≤ ⟪cjm I.ωE I.ωP (I.C ∘L I.Gm.W) f, cjp I.ωE I.ωP (I.C ∘L I.Gm.W) f⟫ :=
    pair_aux ((I.C ∘L I.Gm.W) f) _ _ I.δCW hδCW ‖f‖ (I.CW_diff f) (I.inv.CW_diff f) hf0
  have c1 : 2 * ‖I.C (I.Gm.W f)‖ * (I.δCW * ‖f‖) ≤ ‖I.C (I.Gm.W f)‖ ^ 2 / 4 + 4 * (I.δCW * ‖f‖) ^ 2 := by
    nlinarith [sq_nonneg (‖I.C (I.Gm.W f)‖ / 2 - 2 * (I.δCW * ‖f‖))]
  have B1 : (3 / 4) * ‖I.C (I.Gm.W f)‖ ^ 2 - 5 * (I.δCW * ‖f‖) ^ 2
      ≤ ⟪cjm I.ωE I.ωP (I.C ∘L I.Gm.W) f, cjp I.ωE I.ωP (I.C ∘L I.Gm.W) f⟫ := by linarith
  -- T term
  have A3 : ‖I.Gm.T f‖ ^ 2 - 2 * ‖I.Gm.T f‖ * (I.Gm.dT * ‖f‖) - (I.Gm.dT * ‖f‖) ^ 2
      ≤ ⟪cjm I.ωE I.ωS I.Gm.T f, cjp I.ωE I.ωS I.Gm.T f⟫ :=
    pair_aux (I.Gm.T f) _ _ I.Gm.dT hdT ‖f‖ (I.Gm.T_diff f) (I.inv.Gm.T_diff f) hf0
  have c3 : 2 * ‖I.Gm.T f‖ * (I.Gm.dT * ‖f‖) ≤ ‖I.Gm.T f‖ ^ 2 / 4 + 4 * (I.Gm.dT * ‖f‖) ^ 2 := by
    nlinarith [sq_nonneg (‖I.Gm.T f‖ / 2 - 2 * (I.Gm.dT * ‖f‖))]
  have B3 : (3 / 4) * ‖I.Gm.T f‖ ^ 2 - 5 * (I.Gm.dT * ‖f‖) ^ 2
      ≤ ⟪cjm I.ωE I.ωS I.Gm.T f, cjp I.ωE I.ωS I.Gm.T f⟫ := by linarith
  -- mass term
  have hBp := SiteHyp.norm_op_le _ _ I.hBp f
  have hBm := SiteHyp.norm_op_le _ _ I.hBm f
  rw [ContinuousLinearMap.sub_apply] at hBp hBm
  have A4 := pair_aux (I.Qb f) _ _ I.δB I.hδB ‖f‖ hBp hBm hf0
  have c4 : 2 * ‖I.Qb f‖ * (I.δB * ‖f‖) ≤ ‖I.Qb f‖ ^ 2 / 4 + 4 * (I.δB * ‖f‖) ^ 2 := by
    nlinarith [sq_nonneg (‖I.Qb f‖ / 2 - 2 * (I.δB * ‖f‖))]
  have B4' : (3 / 4) * ‖I.Qb f‖ ^ 2 - 5 * (I.δB * ‖f‖) ^ 2 ≤ ⟪cjm I.ωE I.ωB I.Qb f, cjp I.ωE I.ωB I.Qb f⟫ := by
    linarith
  have B4 := mul_le_mul_of_nonneg_left B4' I.hM
  -- Δ' term
  have hw : ‖I.Gm.W f‖ ≤ I.nW * ‖f‖ := I.Gm.W_le f
  have hwp : ‖cjp I.ωE I.ωE I.Gm.W f - I.Gm.W f‖ ≤ I.Gm.dW * ‖f‖ := I.Gm.W_diff f
  have hwm : ‖cjm I.ωE I.ωE I.Gm.W f - I.Gm.W f‖ ≤ I.Gm.dW * ‖f‖ := I.inv.Gm.W_diff f
  have A2 : ⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫ - I.EA2 * ‖f‖ ^ 2
      ≤ ⟪cjm I.ωE I.ωE I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫ := by
    have e : ⟪cjm I.ωE I.ωE I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫
        = ⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫ + ⟪I.Gm.W f, I.Dp (cjp I.ωE I.ωE I.Gm.W f - I.Gm.W f)⟫
        + ⟪I.Gm.W f, (cjp I.ωE I.ωE I.Dp - I.Dp) (cjp I.ωE I.ωE I.Gm.W f)⟫
        + ⟪cjm I.ωE I.ωE I.Gm.W f - I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫ := by
      simp only [ContinuousLinearMap.sub_apply, map_sub, inner_sub_left, inner_sub_right]; ring
    rw [e]
    have hwp' : ‖cjp I.ωE I.ωE I.Gm.W f‖ ≤ (I.nW + I.Gm.dW) * ‖f‖ := by
      have : cjp I.ωE I.ωE I.Gm.W f = I.Gm.W f + (cjp I.ωE I.ωE I.Gm.W f - I.Gm.W f) := by abel
      rw [this]; refine (norm_add_le _ _).trans ?_; nlinarith
    have hcjDp : ‖cjp I.ωE I.ωE I.Dp‖ ≤ I.ν + I.δν := by
      have : cjp I.ωE I.ωE I.Dp = I.Dp + (cjp I.ωE I.ωE I.Dp - I.Dp) := by abel
      rw [this]; exact (norm_add_le _ _).trans (add_le_add I.hDpn I.hDpp)
    have t1 : |⟪I.Gm.W f, I.Dp (cjp I.ωE I.ωE I.Gm.W f - I.Gm.W f)⟫| ≤ (I.nW * ‖f‖) * (I.ν * (I.Gm.dW * ‖f‖)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hw ((SiteHyp.norm_op_le _ _ I.hDpn _).trans
        (mul_le_mul_of_nonneg_left hwp I.hν)) (norm_nonneg _) (by positivity))
    have t2 : |⟪I.Gm.W f, (cjp I.ωE I.ωE I.Dp - I.Dp) (cjp I.ωE I.ωE I.Gm.W f)⟫|
        ≤ (I.nW * ‖f‖) * (I.δν * ((I.nW + I.Gm.dW) * ‖f‖)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hw ((SiteHyp.norm_op_le _ _ I.hDpp _).trans
        (mul_le_mul_of_nonneg_left hwp' I.hδν)) (norm_nonneg _) (by positivity))
    have t3 : |⟪cjm I.ωE I.ωE I.Gm.W f - I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫|
        ≤ (I.Gm.dW * ‖f‖) * ((I.ν + I.δν) * ((I.nW + I.Gm.dW) * ‖f‖)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hwm ((SiteHyp.norm_op_le _ _ hcjDp _).trans
        (mul_le_mul_of_nonneg_left hwp' (by linarith [I.hν, I.hδν]))) (norm_nonneg _) (by positivity))
    have e2 : I.EA2 * ‖f‖ ^ 2 = (I.nW * ‖f‖) * (I.ν * (I.Gm.dW * ‖f‖))
        + (I.nW * ‖f‖) * (I.δν * ((I.nW + I.Gm.dW) * ‖f‖))
        + (I.Gm.dW * ‖f‖) * ((I.ν + I.δν) * ((I.nW + I.Gm.dW) * ‖f‖)) := by unfold EA2; ring
    have n1 := neg_abs_le ⟪I.Gm.W f, I.Dp (cjp I.ωE I.ωE I.Gm.W f - I.Gm.W f)⟫
    have n2 := neg_abs_le ⟪I.Gm.W f, (cjp I.ωE I.ωE I.Dp - I.Dp) (cjp I.ωE I.ωE I.Gm.W f)⟫
    have n3 := neg_abs_le ⟪cjm I.ωE I.ωE I.Gm.W f - I.Gm.W f, cjp I.ωE I.ωE I.Dp (cjp I.ωE I.ωE I.Gm.W f)⟫
    linarith
  have hDw : -(I.ν * I.nW ^ 2 * ‖f‖ ^ 2) ≤ ⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫ := by
    have h1 : |⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫| ≤ ‖I.Gm.W f‖ * (I.ν * ‖I.Gm.W f‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (SiteHyp.norm_op_le _ _ I.hDpn _) (norm_nonneg _))
    have h2 : ‖I.Gm.W f‖ * (I.ν * ‖I.Gm.W f‖) ≤ I.ν * (I.nW * ‖f‖) ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hw 2
      nlinarith [I.hν]
    have := neg_abs_le ⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫
    nlinarith
  have hEexp : I.EG * ‖f‖ ^ 2
      = (1 / 4) * (I.ν * I.nW ^ 2 * ‖f‖ ^ 2) + 5 * (I.δCW * ‖f‖) ^ 2 + 5 * (I.Gm.dT * ‖f‖) ^ 2
        + I.M * (5 * (I.δB * ‖f‖) ^ 2) + I.EA2 * ‖f‖ ^ 2 := by unfold EG; ring
  have hM34 : I.M * ((3 / 4) * ‖I.Qb f‖ ^ 2 - 5 * (I.δB * ‖f‖) ^ 2)
      = (3 / 4) * (I.M * ‖I.Qb f‖ ^ 2) - I.M * (5 * (I.δB * ‖f‖) ^ 2) := by ring
  rw [hM34] at B4
  rw [hEexp]
  linarith [B1, B3, B4, A2, hDw]

/-- **the weighted bound of `G`**: `(cg/2) ‖Gi⁺ g‖ ≤ ‖g‖`. -/
theorem G_cjp_le (Gi : E →L[ℝ] E) (hGi : ∀ x, I.Ginv (Gi x) = x) (cg : ℝ) (hcg : 0 < cg)
    (hcoer : ∀ f, cg * ‖f‖ ^ 2 ≤ ⟪f, I.Ginv f⟫) (hE : 4 * I.EG ≤ cg) (g : E) :
    (cg / 2) * ‖cjp I.ωE I.ωE Gi g‖ ≤ ‖g‖ := by
  refine inv_cjp_bound I.ωE I.Ginv Gi hGi (cg / 2) (fun h => ?_) g
  have h1 := I.Ginv_CT h
  have h2 := hcoer h
  have h3 := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖h‖)
  nlinarith [sq_nonneg ‖h‖]

end GinvHyp

#print axioms GinvHyp.cjpGinv_form
#print axioms GinvHyp.pair_aux
#print axioms GinvHyp.dZ_nonneg
#print axioms GinvHyp.Ginv_CT
#print axioms GinvHyp.G_cjp_le

end AdalyFormal.DLayer
