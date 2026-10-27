import DLR17

/-!
# DL18 -- the weighted Schur complement `N = Q G Q*` and `H = G Q* N⁻¹` (abstract)

`NHyp` = `GinvHyp` + a two-sided inverse `Gi` of `G⁻¹`, coercivity `cg`, `4E_G ≤ cg`, `‖Qb‖ ≤ qb`, a bond right inverse with
`⟪g,G⁻¹g⟫ ≤ bN‖u‖²` (the competitor), and a two-sided inverse `Ninv` of `N`.
* `N_lower` : `⟪u,Nu⟫ ≥ ‖u‖²/bN` (Cauchy–Schwarz in the `G⁻¹` form; the sharp lower bound needs ONLY the competitor energy);
* `cjpN_lower` : `⟪u,N⁺u⟫ ≥ ⟪u,Nu⟫ − E_N‖u‖²` (explicit `EN`); `Ninv_cjp` : `cN ‖(N⁻¹)⁺w‖ ≤ ‖w‖` for `cN = 1/bN − E_N > 0`;
* **`H_cjp`** : `‖H⁺w‖ ≤ (2/cg)(qb+δB)(1/cN)‖w‖`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

structure NHyp (S E Y P B : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    extends GinvHyp S E Y P B where
  Gi : E →L[ℝ] E
  Ninv : B →L[ℝ] B
  cg : ℝ
  qb : ℝ
  bN : ℝ
  hGi1 : ∀ x, toGinvHyp.Ginv (Gi x) = x
  hGi2 : ∀ x, Gi (toGinvHyp.Ginv x) = x
  hcg : 0 < cg
  hcoerG : ∀ f, cg * ‖f‖ ^ 2 ≤ ⟪f, toGinvHyp.Ginv f⟫
  hEG : 4 * toGinvHyp.EG ≤ cg
  hqb : 0 ≤ qb
  hQb : ‖Qb‖ ≤ qb
  hbN : 0 < bN
  extN : ∀ u : B, ∃ g : E, Qb g = u ∧ ⟪g, toGinvHyp.Ginv g⟫ ≤ bN * ‖u‖ ^ 2
  hN1 : ∀ u, (Qb ∘L Gi ∘L ContinuousLinearMap.adjoint Qb) (Ninv u) = u
  hN2 : ∀ u, Ninv ((Qb ∘L Gi ∘L ContinuousLinearMap.adjoint Qb) u) = u

namespace NHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (J : NHyp S E Y P B)

noncomputable abbrev Iv : GinvHyp S E Y P B := J.toGinvHyp

noncomputable def N : B →L[ℝ] B := J.Qb ∘L J.Gi ∘L ContinuousLinearMap.adjoint J.Qb
noncomputable def H : B →L[ℝ] E := J.Gi ∘L ContinuousLinearMap.adjoint J.Qb ∘L J.Ninv

theorem Ginv_sym (x y : E) : ⟪J.Iv.Ginv x, y⟫ = ⟪x, J.Iv.Ginv y⟫ := by
  simp only [GinvHyp.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  rw [J.hDps]

theorem Gi_sym (x y : E) : ⟪J.Gi x, y⟫ = ⟪x, J.Gi y⟫ := by
  have h := J.Ginv_sym (J.Gi x) (J.Gi y)
  rw [J.hGi1, J.hGi1] at h
  rw [h]

theorem Gi_le (x : E) : J.cg * ‖J.Gi x‖ ≤ ‖x‖ := by
  have h := inv_cjp_bound (WPair.one E) J.Iv.Ginv J.Gi J.hGi1 J.cg (fun h => by rw [cjp_one]; exact J.hcoerG h) x
  rwa [cjp_one] at h

theorem Gi_cjp (x : E) : (J.cg / 2) * ‖cjp J.ωE J.ωE J.Gi x‖ ≤ ‖x‖ :=
  J.Iv.G_cjp_le J.Gi J.hGi1 J.cg J.hcg J.hcoerG J.hEG x

theorem Gi_cjm (x : E) : (J.cg / 2) * ‖cjm J.ωE J.ωE J.Gi x‖ ≤ ‖x‖ :=
  J.Iv.inv.G_cjp_le J.Gi J.hGi1 J.cg J.hcg J.hcoerG J.hEG x

/-- the sharp lower bound of `N` from the competitor -/
theorem N_lower (u : B) : ‖u‖ ^ 2 ≤ J.bN * ⟪u, J.N u⟫ := by
  obtain ⟨g, hg, hgE⟩ := J.extN u
  set x := J.Gi (ContinuousLinearMap.adjoint J.Qb u)
  have hx : J.Iv.Ginv x = ContinuousLinearMap.adjoint J.Qb u := J.hGi1 _
  have hNu : ⟪u, J.N u⟫ = ⟪x, J.Iv.Ginv x⟫ := by
    rw [hx, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]; rfl
  have e1 : ‖u‖ ^ 2 = ⟪x, J.Iv.Ginv g⟫ := by
    rw [← J.Ginv_sym, hx, ContinuousLinearMap.adjoint_inner_left, hg, real_inner_self_eq_norm_sq]
  have hpos : ∀ y, 0 ≤ ⟪y, J.Iv.Ginv y⟫ := fun y => le_trans (by have := J.hcg; positivity) (J.hcoerG y)
  have hCS : ⟪x, J.Iv.Ginv g⟫ ^ 2 ≤ ⟪x, J.Iv.Ginv x⟫ * ⟪g, J.Iv.Ginv g⟫ := by
    have hq' : ∀ t : ℝ, 0 ≤ ⟪x, J.Iv.Ginv x⟫ + 2 * t * ⟪x, J.Iv.Ginv g⟫ + t ^ 2 * ⟪g, J.Iv.Ginv g⟫ := by
      intro t
      have := hpos (x + t • g)
      have e : ⟪x + t • g, J.Iv.Ginv (x + t • g)⟫
          = ⟪x, J.Iv.Ginv x⟫ + 2 * t * ⟪x, J.Iv.Ginv g⟫ + t ^ 2 * ⟪g, J.Iv.Ginv g⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        have : ⟪g, J.Iv.Ginv x⟫ = ⟪x, J.Iv.Ginv g⟫ := by rw [← J.Ginv_sym, real_inner_comm]
        rw [this]; ring
      rw [e] at this; exact this
    by_cases hg0 : ⟪g, J.Iv.Ginv g⟫ = 0
    · have hx0 : ⟪x, J.Iv.Ginv g⟫ = 0 := by
        by_contra hne
        have ht := hq' (-(⟪x, J.Iv.Ginv x⟫ + 1) / (2 * ⟪x, J.Iv.Ginv g⟫))
        have e : 2 * (-(⟪x, J.Iv.Ginv x⟫ + 1) / (2 * ⟪x, J.Iv.Ginv g⟫)) * ⟪x, J.Iv.Ginv g⟫
            = -(⟪x, J.Iv.Ginv x⟫ + 1) := by field_simp
        rw [hg0, e] at ht
        linarith [ht, mul_zero ((-(⟪x, J.Iv.Ginv x⟫ + 1) / (2 * ⟪x, J.Iv.Ginv g⟫)) ^ 2)]
      rw [hx0, hg0]; simp
    · have hgpos : 0 < ⟪g, J.Iv.Ginv g⟫ := lt_of_le_of_ne (hpos g) (Ne.symm hg0)
      have := hq' (-⟪x, J.Iv.Ginv g⟫ / ⟪g, J.Iv.Ginv g⟫)
      have e : ⟪x, J.Iv.Ginv x⟫ + 2 * (-⟪x, J.Iv.Ginv g⟫ / ⟪g, J.Iv.Ginv g⟫) * ⟪x, J.Iv.Ginv g⟫
          + (-⟪x, J.Iv.Ginv g⟫ / ⟪g, J.Iv.Ginv g⟫) ^ 2 * ⟪g, J.Iv.Ginv g⟫
          = ⟪x, J.Iv.Ginv x⟫ - ⟪x, J.Iv.Ginv g⟫ ^ 2 / ⟪g, J.Iv.Ginv g⟫ := by field_simp; ring
      rw [e] at this
      have h2 : ⟪x, J.Iv.Ginv g⟫ ^ 2 / ⟪g, J.Iv.Ginv g⟫ ≤ ⟪x, J.Iv.Ginv x⟫ := by linarith
      rwa [div_le_iff₀ hgpos] at h2
  have h4 : ‖u‖ ^ 4 ≤ ⟪x, J.Iv.Ginv x⟫ * (J.bN * ‖u‖ ^ 2) := by
    have : ‖u‖ ^ 4 = ⟪x, J.Iv.Ginv g⟫ ^ 2 := by rw [← e1]; ring
    rw [this]
    exact hCS.trans (mul_le_mul_of_nonneg_left hgE (hpos x))
  rw [hNu]
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0]; exact mul_nonneg J.hbN.le (hpos x)
  have hu2 : 0 < ‖u‖ ^ 2 := by have := norm_nonneg u; positivity
  nlinarith

end NHyp

#print axioms NHyp.Ginv_sym
#print axioms NHyp.Gi_sym
#print axioms NHyp.Gi_le
#print axioms NHyp.Gi_cjp
#print axioms NHyp.Gi_cjm
#print axioms NHyp.N_lower

end AdalyFormal.DLayer
