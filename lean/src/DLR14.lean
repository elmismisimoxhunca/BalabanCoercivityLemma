import DLR13

/-!
# DL14 -- `T = (1 − XΓ⁻¹X*) D*`, `Z = G'T`, `W = 1 − DZ` under the weights (abstract)

`F = D X` (`Y → E`), `T = D* − X Γ⁻¹ F*`, `Z = G' T`, `W = 1 − D Z`.
* `Linv_unw` : `‖G'y‖ ≤ ‖y‖/c`, `‖DG'y‖ ≤ ‖y‖/√c`;  `LinvDadj_unw` : `‖G'D*v‖ ≤ ‖v‖/√c`, `‖DG'D*v‖ ≤ ‖v‖`.
* `cjmF_le` (`‖F⁻u‖ ≤ kF‖u‖`), `cjmF_diff` (`‖F⁻u − Fu‖ ≤ dF‖u‖`), `cjpX_le` (`‖X⁺u‖ ≤ nX‖u‖`).
* `T_diff` (`‖T⁺v − Tv‖ ≤ dT‖v‖`), `Z_le` (`‖Z⁺v‖ ≤ kZ‖v‖`, `‖DZ⁺v‖ ≤ kDZ‖v‖`), `Z_diff` (`‖Z⁺v − Zv‖ ≤ dZ‖v‖`,
  `‖D(Z⁺v − Zv)‖ ≤ dDZ‖v‖`), `W_diff` (`‖W⁺v − Wv‖ ≤ dW‖v‖`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace GamHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (G : GamHyp S E Y)

theorem Linv_unw (y : S) : ‖G.Linv y‖ ≤ ‖y‖ / G.c ∧ ‖G.D (G.Linv y)‖ ≤ ‖y‖ / Real.sqrt G.c := by
  have hc := G.hc
  have h1 := G.H.Linv_le y
  refine ⟨by rw [le_div_iff₀ hc]; linarith, ?_⟩
  set x := G.Linv y
  have hLx : G.H.L x = y := G.H.L_Linv y
  have hf := G.H.L_form x
  rw [hLx] at hf
  have hm2 : 0 ≤ G.m * ‖G.Qp x‖ ^ 2 := mul_nonneg G.hm (sq_nonneg _)
  have h2 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
  have hx : ‖x‖ ≤ ‖y‖ / G.c := by rw [le_div_iff₀ hc]; linarith
  have hD2 : ‖G.D x‖ ^ 2 ≤ (‖y‖ / Real.sqrt G.c) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hc.le]
    have : ‖x‖ * ‖y‖ ≤ (‖y‖ / G.c) * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have e : (‖y‖ / G.c) * ‖y‖ = ‖y‖ ^ 2 / G.c := by ring
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hD2

theorem LinvDadj_unw (v : E) :
    ‖G.Linv (ContinuousLinearMap.adjoint G.D v)‖ ≤ ‖v‖ / Real.sqrt G.c ∧
    ‖G.D (G.Linv (ContinuousLinearMap.adjoint G.D v))‖ ≤ ‖v‖ := by
  have hc := G.hc
  set x := G.Linv (ContinuousLinearMap.adjoint G.D v)
  have hLx : G.H.L x = ContinuousLinearMap.adjoint G.D v := G.H.L_Linv _
  have hf := G.H.L_form x
  rw [hLx, ContinuousLinearMap.adjoint_inner_right] at hf
  have hm2 : 0 ≤ G.m * ‖G.Qp x‖ ^ 2 := mul_nonneg G.hm (sq_nonneg _)
  have h2 : ⟪G.D x, v⟫ ≤ ‖G.D x‖ * ‖v‖ := real_inner_le_norm _ _
  have hco : G.c * ‖x‖ ^ 2 ≤ ⟪x, G.H.L x⟫ := G.hcoer x
  rw [hLx, ContinuousLinearMap.adjoint_inner_right] at hco
  have hDx : ‖G.D x‖ ≤ ‖v‖ := by
    by_cases h0 : ‖G.D x‖ = 0
    · rw [h0]; exact norm_nonneg _
    have hp : 0 < ‖G.D x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖G.D x‖ * ‖G.D x‖ ≤ ‖v‖ * ‖G.D x‖ := by nlinarith
    exact le_of_mul_le_mul_right this hp
  refine ⟨?_, hDx⟩
  have hx2 : ‖x‖ ^ 2 ≤ (‖v‖ / Real.sqrt G.c) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hc.le, le_div_iff₀ hc]
    have : ‖G.D x‖ * ‖v‖ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right hDx (norm_nonneg _)
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hx2

/-! ## constants -/
noncomputable def nX : ℝ := G.q / G.c + G.H.epsX G.q
noncomputable def nDX : ℝ := G.q / Real.sqrt G.c + G.H.epsDX G.q
noncomputable def kF : ℝ := G.nDX + G.δD * G.nX
noncomputable def dF : ℝ := G.δD * G.nX + G.H.epsDX G.q
noncomputable def gi : ℝ := 1 / G.cG
noncomputable def dT : ℝ := G.δD + G.H.epsX G.q * G.gi * G.kF + (G.q / G.c) * G.dGi * G.kF + (G.q / G.c) * G.gi * G.dF
noncomputable def kZ : ℝ := Real.sqrt (48 / G.c) + (4 / G.c) * G.nX * G.gi * G.kF
noncomputable def kDZ : ℝ := Real.sqrt 24 + Real.sqrt (12 / G.c) * G.nX * G.gi * G.kF
noncomputable def dZ : ℝ := (8 / G.c) * G.δD + G.H.K0 G.q / Real.sqrt G.c
  + ((4 / G.c) * G.δD / Real.sqrt G.c + G.H.K0 G.q / G.c) * G.nX * G.gi * G.kF
  + (1 / G.c) * G.H.epsX G.q * G.gi * G.kF + (1 / G.c) * (G.q / G.c) * G.dGi * G.kF
  + (1 / G.c) * (G.q / G.c) * G.gi * G.dF
noncomputable def dDZ : ℝ := 2 * Real.sqrt (12 / G.c) * G.δD + G.H.K1 G.q / Real.sqrt G.c
  + (Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 G.q / G.c) * G.nX * G.gi * G.kF
  + (1 / Real.sqrt G.c) * G.H.epsX G.q * G.gi * G.kF + (1 / Real.sqrt G.c) * (G.q / G.c) * G.dGi * G.kF
  + (1 / Real.sqrt G.c) * (G.q / G.c) * G.gi * G.dF
noncomputable def dW : ℝ := G.δD * G.kZ + G.dDZ

theorem consts_nonneg : 0 ≤ G.nX ∧ 0 ≤ G.nDX ∧ 0 ≤ G.kF ∧ 0 ≤ G.dF ∧ 0 ≤ G.gi ∧ 0 ≤ G.dGi := by
  have hc := G.hc; have hq := G.hq; have hδD := G.hδD; have hcG := G.hcG
  have he := G.H.epsX_nonneg G.q G.hq
  have hed : 0 ≤ G.H.epsDX G.q := by
    unfold SiteHyp.epsDX; have := G.H.K1_nonneg G.q G.hq; have := G.hδQ; positivity
  have hdG : 0 ≤ G.dGam := by unfold dGam; positivity
  refine ⟨by unfold nX; positivity, by unfold nDX; positivity, by unfold kF nDX nX; positivity,
    by unfold dF nX; positivity, by unfold gi; positivity, by unfold dGi; positivity⟩

/-! ## `F = D X` -/
noncomputable def F : Y →L[ℝ] E := G.D ∘L G.H.X

theorem cjmF_eq : cjm G.ωY G.ωE G.F = cjm G.ωS G.ωE G.D ∘L cjm G.ωY G.ωS G.H.X := by
  rw [F, cjm_comp G.ωY G.ωS G.ωE]

theorem cjX_le (u : Y) : ‖cjp G.ωY G.ωS G.H.X u‖ ≤ G.nX * ‖u‖ ∧ ‖cjm G.ωY G.ωS G.H.X u‖ ≤ G.nX * ‖u‖ ∧
    ‖G.D (cjp G.ωY G.ωS G.H.X u)‖ ≤ G.nDX * ‖u‖ ∧ ‖G.D (cjm G.ωY G.ωS G.H.X u)‖ ≤ G.nDX * ‖u‖ := by
  obtain ⟨p1, p2⟩ := G.H.Xdiff G.q G.hq G.hQ u
  obtain ⟨m1, m2⟩ := G.H.Xdiff_m G.q G.hq G.hQ u
  have hX := G.H.X_le G.q G.hQ u
  have hDX := G.H.DX_le G.q G.hq G.hQ u
  have e1 : cjp G.ωY G.ωS G.H.X u = G.H.X u + (cjp G.ωY G.ωS G.H.X u - G.H.X u) := by abel
  have e2 : cjm G.ωY G.ωS G.H.X u = G.H.X u + (cjm G.ωY G.ωS G.H.X u - G.H.X u) := by abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; refine (norm_add_le _ _).trans ?_; unfold nX; linarith
  · rw [e2]; refine (norm_add_le _ _).trans ?_; unfold nX; linarith
  · rw [e1, map_add]; refine (norm_add_le _ _).trans ?_; unfold nDX; linarith
  · rw [e2, map_add]; refine (norm_add_le _ _).trans ?_; unfold nDX; linarith

theorem cjmF_bounds (u : Y) : ‖cjm G.ωY G.ωE G.F u‖ ≤ G.kF * ‖u‖ ∧ ‖cjm G.ωY G.ωE G.F u - G.F u‖ ≤ G.dF * ‖u‖ := by
  rw [cjmF_eq, ContinuousLinearMap.comp_apply]
  obtain ⟨-, hm, -, hDm⟩ := G.cjX_le u
  obtain ⟨m1, m2⟩ := G.H.Xdiff_m G.q G.hq G.hQ u
  set w := cjm G.ωY G.ωS G.H.X u
  have hδ : ‖(cjm G.ωS G.ωE G.D - G.D) w‖ ≤ G.δD * (G.nX * ‖u‖) :=
    (SiteHyp.norm_op_le _ _ G.hDm w).trans (mul_le_mul_of_nonneg_left hm G.hδD)
  have e : cjm G.ωS G.ωE G.D w = G.D w + (cjm G.ωS G.ωE G.D - G.D) w := by
    rw [ContinuousLinearMap.sub_apply]; abel
  have hF : G.F u = G.D (G.H.X u) := rfl
  refine ⟨?_, ?_⟩
  · rw [e]; refine (norm_add_le _ _).trans ?_; unfold kF; nlinarith [norm_nonneg u]
  · rw [e, hF]
    have e2 : G.D w + (cjm G.ωS G.ωE G.D - G.D) w - G.D (G.H.X u)
        = G.D (w - G.H.X u) + (cjm G.ωS G.ωE G.D - G.D) w := by rw [map_sub]; abel
    rw [e2]; refine (norm_add_le _ _).trans ?_
    unfold dF; nlinarith [norm_nonneg u]

#print axioms Linv_unw
#print axioms LinvDadj_unw
#print axioms consts_nonneg
#print axioms cjmF_eq
#print axioms cjX_le
#print axioms cjmF_bounds

end GamHyp

end AdalyFormal.DLayer
