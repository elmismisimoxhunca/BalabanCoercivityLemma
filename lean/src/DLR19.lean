import DLR18

/-!
# DL19 -- weighted `N⁻¹` and `H` (abstract)

* `cjpGinv_bil` / `Ginv_bil` : the bilinear forms `⟪y,(G⁻¹)⁺x⟫`, `⟪y,G⁻¹x⟫` in the pieces `CW, W Δ' W, T, √M Qb`.
* `energy_x`, `energy_y` : the piece energies of `x = G Qb*u` and `y = G⁻ Qb*u` are `≤ Ex‖u‖²`, `≤ Ey‖u‖²`.
* `cjpN_lower` : `⟪u,N⁺u⟫ ≥ ⟪u,Nu⟫ − E_N‖u‖²`;  `Ninv_cjp` : `cN‖(N⁻¹)⁺w‖ ≤ ‖w‖` (`cN = 1/bN − E_N > 0`);
* **`H_cjp`** : `‖H⁺w‖ ≤ (2/cg)(qb+δB)(1/cN)‖w‖`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace NHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (J : NHyp S E Y P B)

theorem Ginv_bil (y x : E) : ⟪y, J.Iv.Ginv x⟫
    = ⟪J.C (J.Iv.Gm.W y), J.C (J.Iv.Gm.W x)⟫ + ⟪J.Iv.Gm.W y, J.Dp (J.Iv.Gm.W x)⟫ + ⟪J.Iv.Gm.T y, J.Iv.Gm.T x⟫
      + J.M * ⟪J.Qb y, J.Qb x⟫ := by
  simp only [GinvHyp.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_add_left]

theorem cjpGinv_bil (y x : E) : ⟪y, cjp J.ωE J.ωE J.Iv.Ginv x⟫
    = ⟪cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) y, cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) x⟫
      + ⟪cjm J.ωE J.ωE J.Iv.Gm.W y, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W x)⟫
      + ⟪cjm J.ωE J.ωS J.Iv.Gm.T y, cjp J.ωE J.ωS J.Iv.Gm.T x⟫
      + J.M * ⟪cjm J.ωE J.ωB J.Qb y, cjp J.ωE J.ωB J.Qb x⟫ := by
  have e1 : cjp J.ωE J.ωE J.Iv.Ginv
      = ContinuousLinearMap.adjoint (cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W)) ∘L cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W)
        + ContinuousLinearMap.adjoint (cjm J.ωE J.ωE J.Iv.Gm.W) ∘L cjp J.ωE J.ωE J.Dp ∘L cjp J.ωE J.ωE J.Iv.Gm.W
        + ContinuousLinearMap.adjoint (cjm J.ωE J.ωS J.Iv.Gm.T) ∘L cjp J.ωE J.ωS J.Iv.Gm.T
        + J.M • (ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) ∘L cjp J.ωE J.ωB J.Qb) := by
    have hsplit : J.Iv.Ginv = ContinuousLinearMap.adjoint (J.C ∘L J.Iv.Gm.W) ∘L (J.C ∘L J.Iv.Gm.W)
        + ContinuousLinearMap.adjoint J.Iv.Gm.W ∘L J.Dp ∘L J.Iv.Gm.W
        + ContinuousLinearMap.adjoint J.Iv.Gm.T ∘L J.Iv.Gm.T + J.M • (ContinuousLinearMap.adjoint J.Qb ∘L J.Qb) := by
      ext v
      simp only [GinvHyp.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.adjoint_comp, map_add]
    rw [hsplit, cjp_add, cjp_add, cjp_add, cjp_smul, cjp_comp J.ωE J.ωP J.ωE, cjp_comp J.ωE J.ωE J.ωE,
      cjp_comp J.ωE J.ωE J.ωE, cjp_comp J.ωE J.ωS J.ωE, cjp_comp J.ωE J.ωB J.ωE,
      adjoint_cjm, adjoint_cjm, adjoint_cjm, adjoint_cjm]
  rw [e1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]

/-- piece energy: `‖CWz‖² + ‖Tz‖² + M‖Qb z‖² ≤ ⟪z,G⁻¹z⟫ + ν nW²‖z‖²` -/
theorem pieces_le (z : E) :
    ‖J.C (J.Iv.Gm.W z)‖ ^ 2 + ‖J.Iv.Gm.T z‖ ^ 2 + J.M * ‖J.Qb z‖ ^ 2 ≤ ⟪z, J.Iv.Ginv z⟫ + J.ν * J.Iv.nW ^ 2 * ‖z‖ ^ 2 := by
  rw [J.Iv.Ginv_form]
  have hw : ‖J.Iv.Gm.W z‖ ≤ J.Iv.nW * ‖z‖ := J.Iv.Gm.W_le z
  have h1 : |⟪J.Iv.Gm.W z, J.Dp (J.Iv.Gm.W z)⟫| ≤ ‖J.Iv.Gm.W z‖ * (J.ν * ‖J.Iv.Gm.W z‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (SiteHyp.norm_op_le _ _ J.hDpn _) (norm_nonneg _))
  have h2 : ‖J.Iv.Gm.W z‖ * (J.ν * ‖J.Iv.Gm.W z‖) ≤ J.ν * (J.Iv.nW * ‖z‖) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith [J.hν]
  have := neg_abs_le ⟪J.Iv.Gm.W z, J.Dp (J.Iv.Gm.W z)⟫
  nlinarith

/-- generic bilinear difference -/
theorem bil_diff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (p pm q qp : V) (dp dq : ℝ)
    (hp : ‖pm - p‖ ≤ dp) (hq : ‖qp - q‖ ≤ dq) :
    |⟪pm, qp⟫ - ⟪p, q⟫| ≤ dp * (‖q‖ + dq) + ‖p‖ * dq := by
  have e : ⟪pm, qp⟫ - ⟪p, q⟫ = ⟪pm - p, qp⟫ + ⟪p, qp - q⟫ := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e]
  have hqp : ‖qp‖ ≤ ‖q‖ + dq := by
    have h1 : qp = q + (qp - q) := by abel
    calc ‖qp‖ = ‖q + (qp - q)‖ := congrArg _ h1
      _ ≤ ‖q‖ + ‖qp - q‖ := norm_add_le _ _
      _ ≤ ‖q‖ + dq := by linarith
  have hdp : 0 ≤ dp := le_trans (norm_nonneg _) hp
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hp hqp (norm_nonneg _) hdp)
  · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))

theorem CW_piece (x y : E) :
    |⟪cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) x, cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) y⟫ - ⟪J.C (J.Iv.Gm.W x), J.C (J.Iv.Gm.W y)⟫|
      ≤ J.Iv.δCW * ‖x‖ * (‖J.C (J.Iv.Gm.W y)‖ + J.Iv.δCW * ‖y‖) + ‖J.C (J.Iv.Gm.W x)‖ * (J.Iv.δCW * ‖y‖) :=
  bil_diff (J.C (J.Iv.Gm.W x)) (cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) x) (J.C (J.Iv.Gm.W y))
    (cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) y) (J.Iv.δCW * ‖x‖) (J.Iv.δCW * ‖y‖) (J.Iv.inv.CW_diff x) (J.Iv.CW_diff y)

theorem T_piece (x y : E) :
    |⟪cjm J.ωE J.ωS J.Iv.Gm.T x, cjp J.ωE J.ωS J.Iv.Gm.T y⟫ - ⟪J.Iv.Gm.T x, J.Iv.Gm.T y⟫|
      ≤ J.Iv.Gm.dT * ‖x‖ * (‖J.Iv.Gm.T y‖ + J.Iv.Gm.dT * ‖y‖) + ‖J.Iv.Gm.T x‖ * (J.Iv.Gm.dT * ‖y‖) :=
  bil_diff (J.Iv.Gm.T x) (cjm J.ωE J.ωS J.Iv.Gm.T x) (J.Iv.Gm.T y) (cjp J.ωE J.ωS J.Iv.Gm.T y)
    (J.Iv.Gm.dT * ‖x‖) (J.Iv.Gm.dT * ‖y‖) (J.Iv.inv.Gm.T_diff x) (J.Iv.Gm.T_diff y)

theorem M_piece (x y : E) :
    |⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb y⟫ - ⟪J.Qb x, J.Qb y⟫|
      ≤ J.δB * ‖x‖ * (‖J.Qb y‖ + J.δB * ‖y‖) + ‖J.Qb x‖ * (J.δB * ‖y‖) := by
  have hBp := SiteHyp.norm_op_le _ _ J.hBp y
  have hBm := SiteHyp.norm_op_le _ _ J.hBm x
  rw [ContinuousLinearMap.sub_apply] at hBp hBm
  exact bil_diff (J.Qb x) (cjm J.ωE J.ωB J.Qb x) (J.Qb y) (cjp J.ωE J.ωB J.Qb y) _ _ hBm hBp

/-- the `Δ'` constant -/
noncomputable def KD : ℝ :=
  J.Iv.Gm.dW * ((J.ν + J.δν) * (J.Iv.nW + J.Iv.Gm.dW)) + J.Iv.nW * (J.δν * (J.Iv.nW + J.Iv.Gm.dW) + J.ν * J.Iv.Gm.dW)

theorem nW_nonneg : 0 ≤ J.Iv.nW := by
  obtain ⟨-, hdDZ, -, hkDZ, -, -⟩ := J.Iv.dZ_nonneg
  unfold GinvHyp.nW; linarith

theorem Dp_piece (x y : E) :
    |⟪cjm J.ωE J.ωE J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫ - ⟪J.Iv.Gm.W x, J.Dp (J.Iv.Gm.W y)⟫|
      ≤ J.KD * ‖x‖ * ‖y‖ := by
  have hw : ‖J.Iv.Gm.W x‖ ≤ J.Iv.nW * ‖x‖ := J.Iv.Gm.W_le x
  have hwy : ‖J.Iv.Gm.W y‖ ≤ J.Iv.nW * ‖y‖ := J.Iv.Gm.W_le y
  have hwp : ‖cjp J.ωE J.ωE J.Iv.Gm.W y - J.Iv.Gm.W y‖ ≤ J.Iv.Gm.dW * ‖y‖ := J.Iv.Gm.W_diff y
  have hwm : ‖cjm J.ωE J.ωE J.Iv.Gm.W x - J.Iv.Gm.W x‖ ≤ J.Iv.Gm.dW * ‖x‖ := J.Iv.inv.Gm.W_diff x
  obtain ⟨-, -, -, -, hdW, -⟩ := J.Iv.dZ_nonneg
  have hnW := J.nW_nonneg
  have hν := J.hν
  have hδν := J.hδν
  have hwp' : ‖cjp J.ωE J.ωE J.Iv.Gm.W y‖ ≤ (J.Iv.nW + J.Iv.Gm.dW) * ‖y‖ := by
    have h1 : cjp J.ωE J.ωE J.Iv.Gm.W y = J.Iv.Gm.W y + (cjp J.ωE J.ωE J.Iv.Gm.W y - J.Iv.Gm.W y) := by abel
    rw [h1]; refine (norm_add_le _ _).trans ?_; linarith
  have hcjDp : ‖cjp J.ωE J.ωE J.Dp‖ ≤ J.ν + J.δν := by
    have h1 : cjp J.ωE J.ωE J.Dp = J.Dp + (cjp J.ωE J.ωE J.Dp - J.Dp) := by abel
    rw [h1]; exact (norm_add_le _ _).trans (add_le_add J.hDpn J.hDpp)
  have e : ⟪cjm J.ωE J.ωE J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫
        - ⟪J.Iv.Gm.W x, J.Dp (J.Iv.Gm.W y)⟫
      = ⟪cjm J.ωE J.ωE J.Iv.Gm.W x - J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫
        + ⟪J.Iv.Gm.W x, (cjp J.ωE J.ωE J.Dp - J.Dp) (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫
        + ⟪J.Iv.Gm.W x, J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y - J.Iv.Gm.W y)⟫ := by
    simp only [ContinuousLinearMap.sub_apply, map_sub, inner_sub_left, inner_sub_right]; ring
  rw [e]
  have t1 : |⟪cjm J.ωE J.ωE J.Iv.Gm.W x - J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫|
      ≤ (J.Iv.Gm.dW * ‖x‖) * ((J.ν + J.δν) * ((J.Iv.nW + J.Iv.Gm.dW) * ‖y‖)) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hwm ((SiteHyp.norm_op_le _ _ hcjDp _).trans
      (mul_le_mul_of_nonneg_left hwp' (by linarith))) (norm_nonneg _) (by positivity))
  have t2 : |⟪J.Iv.Gm.W x, (cjp J.ωE J.ωE J.Dp - J.Dp) (cjp J.ωE J.ωE J.Iv.Gm.W y)⟫|
      ≤ (J.Iv.nW * ‖x‖) * (J.δν * ((J.Iv.nW + J.Iv.Gm.dW) * ‖y‖)) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hw ((SiteHyp.norm_op_le _ _ J.hDpp _).trans
      (mul_le_mul_of_nonneg_left hwp' hδν)) (norm_nonneg _) (by positivity))
  have t3 : |⟪J.Iv.Gm.W x, J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W y - J.Iv.Gm.W y)⟫|
      ≤ (J.Iv.nW * ‖x‖) * (J.ν * (J.Iv.Gm.dW * ‖y‖)) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hw ((SiteHyp.norm_op_le _ _ J.hDpn _).trans
      (mul_le_mul_of_nonneg_left hwp hν)) (norm_nonneg _) (by positivity))
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  have e2 : J.KD * ‖x‖ * ‖y‖ = (J.Iv.Gm.dW * ‖x‖) * ((J.ν + J.δν) * ((J.Iv.nW + J.Iv.Gm.dW) * ‖y‖))
      + (J.Iv.nW * ‖x‖) * (J.δν * ((J.Iv.nW + J.Iv.Gm.dW) * ‖y‖)) + (J.Iv.nW * ‖x‖) * (J.ν * (J.Iv.Gm.dW * ‖y‖)) := by
    unfold KD; ring
  rw [e2]; linarith

/-! ### the constants of the weighted Schur complement -/

noncomputable def X0 : ℝ := J.qb / J.cg
noncomputable def Y0 : ℝ := (2 / J.cg) * (J.qb + J.δB)
noncomputable def Ex : ℝ := J.qb * J.X0
noncomputable def Ey : ℝ := (4 / 3) * (J.Iv.EG * J.Y0 ^ 2 + J.Y0 * (J.qb + J.δB))
noncomputable def Px : ℝ := Real.sqrt (J.Ex + J.ν * J.Iv.nW ^ 2 * J.X0 ^ 2)
noncomputable def Py : ℝ := Real.sqrt (J.Ey + J.ν * J.Iv.nW ^ 2 * J.Y0 ^ 2)

/-- the error of `N⁺` -/
noncomputable def EN : ℝ :=
  J.δB * J.Y0 + J.X0 * J.δB
  + (J.Iv.δCW * J.X0 * (J.Py + J.Iv.δCW * J.Y0) + J.Px * (J.Iv.δCW * J.Y0))
  + J.KD * J.X0 * J.Y0
  + (J.Iv.Gm.dT * J.X0 * (J.Py + J.Iv.Gm.dT * J.Y0) + J.Px * (J.Iv.Gm.dT * J.Y0))
  + (J.δB * J.X0 * (Real.sqrt J.M * J.Py) + J.M * J.δB ^ 2 * J.X0 * J.Y0 + Real.sqrt J.M * J.Px * J.δB * J.Y0)

theorem EG_nonneg : 0 ≤ J.Iv.EG := by
  obtain ⟨-, -, -, -, hdW, hdT⟩ := J.Iv.dZ_nonneg
  have hnW := J.nW_nonneg
  have hν := J.hν; have hδν := J.hδν; have hM := J.hM
  unfold GinvHyp.EG GinvHyp.EA2; positivity

theorem consts2_nonneg : 0 ≤ J.X0 ∧ 0 ≤ J.Y0 ∧ 0 ≤ J.Ex ∧ 0 ≤ J.Ey := by
  have hcg := J.hcg; have hqb := J.hqb; have hδB := J.hδB; have hEG := J.EG_nonneg
  have h1 : 0 ≤ J.X0 := by unfold X0; positivity
  have h2 : 0 ≤ J.Y0 := by unfold Y0; positivity
  refine ⟨h1, h2, by unfold Ex; positivity, by unfold Ey; positivity⟩

theorem cjmQb_norm : ‖cjm J.ωE J.ωB J.Qb‖ ≤ J.qb + J.δB := by
  have h1 : cjm J.ωE J.ωB J.Qb = J.Qb + (cjm J.ωE J.ωB J.Qb - J.Qb) := by abel
  rw [h1]; exact (norm_add_le _ _).trans (add_le_add J.hQb J.hBm)

theorem cjpQb_norm : ‖cjp J.ωE J.ωB J.Qb‖ ≤ J.qb + J.δB := by
  have h1 : cjp J.ωE J.ωB J.Qb = J.Qb + (cjp J.ωE J.ωB J.Qb - J.Qb) := by abel
  rw [h1]; exact (norm_add_le _ _).trans (add_le_add J.hQb J.hBp)

/-- squared piece bound ⟹ linear piece bound -/
theorem lin_of_sq (a P r : ℝ) (hP : 0 ≤ P) (hr : 0 ≤ r) (h : a ^ 2 ≤ P ^ 2 * r ^ 2) : a ≤ P * r :=
  (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact h) (mul_nonneg hP hr)).2

/-- piece bounds from an energy bound -/
theorem piece_bounds (z : E) (Z0 Ez r : ℝ) (hEz : 0 ≤ Ez) (hr : 0 ≤ r) (hz : ‖z‖ ≤ Z0 * r)
    (hE : ⟪z, J.Iv.Ginv z⟫ ≤ Ez * r ^ 2) :
    ‖J.C (J.Iv.Gm.W z)‖ ≤ Real.sqrt (Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2) * r ∧
    ‖J.Iv.Gm.T z‖ ≤ Real.sqrt (Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2) * r ∧
    Real.sqrt J.M * ‖J.Qb z‖ ≤ Real.sqrt (Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2) * r := by
  have hp := J.pieces_le z
  have hν := J.hν
  have hM := J.hM
  have hnW := J.nW_nonneg
  have hz2 : ‖z‖ ^ 2 ≤ (Z0 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hk : 0 ≤ J.ν * J.Iv.nW ^ 2 := by positivity
  have hS : ‖J.C (J.Iv.Gm.W z)‖ ^ 2 + ‖J.Iv.Gm.T z‖ ^ 2 + J.M * ‖J.Qb z‖ ^ 2
      ≤ (Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2) * r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hz2 hk
    nlinarith
  have hpos : 0 ≤ Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2 := by positivity
  have hsq : Real.sqrt (Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2) ^ 2 = Ez + J.ν * J.Iv.nW ^ 2 * Z0 ^ 2 := Real.sq_sqrt hpos
  have hT2 := sq_nonneg ‖J.Iv.Gm.T z‖
  have hC2 := sq_nonneg ‖J.C (J.Iv.Gm.W z)‖
  have hQ2 : 0 ≤ J.M * ‖J.Qb z‖ ^ 2 := by positivity
  have hMQ : (Real.sqrt J.M * ‖J.Qb z‖) ^ 2 = J.M * ‖J.Qb z‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hM]
  refine ⟨lin_of_sq _ _ _ (Real.sqrt_nonneg _) hr (by rw [hsq]; linarith),
    lin_of_sq _ _ _ (Real.sqrt_nonneg _) hr (by rw [hsq]; linarith),
    lin_of_sq _ _ _ (Real.sqrt_nonneg _) hr (by rw [hsq, hMQ]; linarith)⟩

end NHyp

#print axioms NHyp.Ginv_bil
#print axioms NHyp.cjpGinv_bil
#print axioms NHyp.pieces_le
#print axioms NHyp.bil_diff
#print axioms NHyp.CW_piece
#print axioms NHyp.T_piece
#print axioms NHyp.M_piece
#print axioms NHyp.Dp_piece
#print axioms NHyp.EG_nonneg
#print axioms NHyp.consts2_nonneg
#print axioms NHyp.piece_bounds

end AdalyFormal.DLayer
