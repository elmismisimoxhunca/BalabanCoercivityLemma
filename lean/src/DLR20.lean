import DLR19

/-!
# DL20 -- weighted `N = Qb G Qb*`, `N⁻¹` and `H = G Qb* N⁻¹` (abstract, explicit constants)

* `cjpN_lower` : `⟪u,N⁺u⟫ ≥ ⟪u,Nu⟫ − E_N‖u‖²` with the explicit `EN` of DL19
  (representation `⟪u,N⁺u⟫ − ⟪u,Nu⟫ = ⟪a⁺−a,y⁺⟫ + ⟪x,b⁻−a⟫ − (⟪x,(G⁻¹)⁺y⁺⟫ − ⟪x,G⁻¹y⁺⟫)`, `x = G Qb*u`, `y⁺ = G⁺(Qb⁻)*u`;
  the last bracket is bounded piece by piece — curl∘W, Δ', T, mass — by the ENERGIES of `x` and `y⁺`, never by `‖G⁻¹‖`).
* `N_cjp_coer` : `⟪u,N⁺u⟫ ≥ (1/bN − E_N)‖u‖²`;  `Ninv_cjp` : `(1/bN − E_N)‖(N⁻¹)⁺w‖ ≤ ‖w‖`.
* **`H_cjp`** : `‖H⁺w‖ ≤ (2/cg)(qb+δB)/(1/bN − E_N) ‖w‖` when `E_N < 1/bN`.
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

theorem cjpN_eq : cjp J.ωB J.ωB J.N
    = cjp J.ωE J.ωB J.Qb ∘L (cjp J.ωE J.ωE J.Gi ∘L ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb)) := by
  rw [N, cjp_comp J.ωB J.ωE J.ωB, cjp_comp J.ωB J.ωE J.ωE, adjoint_cjm]

theorem cjpH_eq : cjp J.ωB J.ωE J.H
    = cjp J.ωE J.ωE J.Gi ∘L (ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) ∘L cjp J.ωB J.ωB J.Ninv) := by
  rw [H, cjp_comp J.ωB J.ωE J.ωE, cjp_comp J.ωB J.ωB J.ωE, adjoint_cjm]

/-- **the weighted Schur complement is a small perturbation in FORM sense** -/
theorem cjpN_lower (u : B) : ⟪u, J.N u⟫ - J.EN * ‖u‖ ^ 2 ≤ ⟪u, cjp J.ωB J.ωB J.N u⟫ := by
  set a0 := ContinuousLinearMap.adjoint J.Qb u with ha0
  set x := J.Gi a0 with hxdef
  set bp := ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) u with hbp
  set ap := ContinuousLinearMap.adjoint (cjp J.ωE J.ωB J.Qb) u with hap
  set yp := cjp J.ωE J.ωE J.Gi bp with hyp
  have hNp : ⟪u, cjp J.ωB J.ωB J.N u⟫ = ⟪ap, yp⟫ := by
    rw [cjpN_eq]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left]
  have hN : ⟪u, J.N u⟫ = ⟪a0, x⟫ := by
    show ⟪u, J.Qb (J.Gi (ContinuousLinearMap.adjoint J.Qb u))⟫ = _
    rw [← ContinuousLinearMap.adjoint_inner_left]
  have hx : J.Iv.Ginv x = a0 := J.hGi1 a0
  have hy : cjp J.ωE J.ωE J.Iv.Ginv yp = bp := by
    rw [hyp, cjp_apply, cjp_apply, J.ωE.wi_w, J.hGi1, J.ωE.w_wi]
  -- the representation
  have h1 : ⟪a0, yp⟫ = ⟪x, J.Iv.Ginv yp⟫ := by rw [← hx, J.Ginv_sym]
  have h2 : ⟪x, bp⟫ = ⟪x, cjp J.ωE J.ωE J.Iv.Ginv yp⟫ := by rw [hy]
  have h3 : ⟪x, a0⟫ = ⟪a0, x⟫ := real_inner_comm _ _
  have hrep : ⟪ap, yp⟫ = ⟪a0, x⟫ + ⟪ap - a0, yp⟫ + ⟪x, bp - a0⟫
      - (⟪x, cjp J.ωE J.ωE J.Iv.Ginv yp⟫ - ⟪x, J.Iv.Ginv yp⟫) := by
    rw [inner_sub_left, inner_sub_right]; linarith
  -- the third bracket, piece by piece
  have hthird : ⟪x, cjp J.ωE J.ωE J.Iv.Ginv yp⟫ - ⟪x, J.Iv.Ginv yp⟫
      = (⟪cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) x, cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) yp⟫
          - ⟪J.C (J.Iv.Gm.W x), J.C (J.Iv.Gm.W yp)⟫)
        + (⟪cjm J.ωE J.ωE J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W yp)⟫
          - ⟪J.Iv.Gm.W x, J.Dp (J.Iv.Gm.W yp)⟫)
        + (⟪cjm J.ωE J.ωS J.Iv.Gm.T x, cjp J.ωE J.ωS J.Iv.Gm.T yp⟫ - ⟪J.Iv.Gm.T x, J.Iv.Gm.T yp⟫)
        + J.M * (⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb yp⟫ - ⟪J.Qb x, J.Qb yp⟫) := by
    rw [J.cjpGinv_bil x yp, J.Ginv_bil x yp]; ring
  -- norm and energy bounds for x and y⁺
  obtain ⟨hX0, hY0, hEx0, hEy0⟩ := J.consts2_nonneg
  have hcg := J.hcg
  have hqb := J.hqb
  have hδB := J.hδB
  have hM := J.hM
  have hu := norm_nonneg u
  have ha0n : ‖a0‖ ≤ J.qb * ‖u‖ := SiteHyp.norm_adj_sub_le _ _ J.hQb u
  have hbpn : ‖bp‖ ≤ (J.qb + J.δB) * ‖u‖ := SiteHyp.norm_adj_sub_le _ _ J.cjmQb_norm u
  have hapd : ‖ap - a0‖ ≤ J.δB * ‖u‖ := by
    have e : ap - a0 = ContinuousLinearMap.adjoint (cjp J.ωE J.ωB J.Qb - J.Qb) u := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [e]; exact SiteHyp.norm_adj_sub_le _ _ J.hBp u
  have hbpd : ‖bp - a0‖ ≤ J.δB * ‖u‖ := by
    have e : bp - a0 = ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb - J.Qb) u := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [e]; exact SiteHyp.norm_adj_sub_le _ _ J.hBm u
  have hxn : ‖x‖ ≤ J.X0 * ‖u‖ := by
    have h := J.Gi_le a0
    have h' : J.cg * ‖x‖ ≤ J.qb * ‖u‖ := h.trans ha0n
    unfold X0
    rw [div_mul_eq_mul_div, le_div_iff₀ hcg]; linarith
  have hyn : ‖yp‖ ≤ J.Y0 * ‖u‖ := by
    have h := J.Gi_cjp bp
    have h' : (J.cg / 2) * ‖yp‖ ≤ (J.qb + J.δB) * ‖u‖ := h.trans hbpn
    unfold Y0
    have e : 2 / J.cg * (J.qb + J.δB) * ‖u‖ = ((J.qb + J.δB) * ‖u‖) / (J.cg / 2) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]; linarith
  have hEx : ⟪x, J.Iv.Ginv x⟫ ≤ J.Ex * ‖u‖ ^ 2 := by
    rw [hx]
    have := (real_inner_le_norm x a0).trans (mul_le_mul hxn ha0n (norm_nonneg _) (by positivity))
    unfold Ex; nlinarith
  have hEy : ⟪yp, J.Iv.Ginv yp⟫ ≤ J.Ey * ‖u‖ ^ 2 := by
    have hct := J.Iv.Ginv_CT yp
    rw [hy] at hct
    have hin := (real_inner_le_norm yp bp).trans (mul_le_mul hyn hbpn (norm_nonneg _) (by positivity))
    have hEG := J.EG_nonneg
    have hy2 : ‖yp‖ ^ 2 ≤ (J.Y0 * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyn 2
    have := mul_le_mul_of_nonneg_left hy2 hEG
    unfold Ey; nlinarith
  obtain ⟨hcx, htx, hqx⟩ := J.piece_bounds x J.X0 J.Ex ‖u‖ hEx0 hu hxn hEx
  obtain ⟨hcy, hty, hqy⟩ := J.piece_bounds yp J.Y0 J.Ey ‖u‖ hEy0 hu hyn hEy
  have hPx : J.Px = Real.sqrt (J.Ex + J.ν * J.Iv.nW ^ 2 * J.X0 ^ 2) := rfl
  have hPy : J.Py = Real.sqrt (J.Ey + J.ν * J.Iv.nW ^ 2 * J.Y0 ^ 2) := rfl
  rw [← hPx] at hcx htx hqx
  rw [← hPy] at hcy hty hqy
  have hPx0 : 0 ≤ J.Px := Real.sqrt_nonneg _
  have hPy0 : 0 ≤ J.Py := Real.sqrt_nonneg _
  obtain ⟨-, -, -, -, hdW, hdT⟩ := J.Iv.dZ_nonneg
  have hδCW : 0 ≤ J.Iv.δCW := by
    unfold GinvHyp.δCW; have := J.hδC; have := J.hδK; have := J.hκ
    obtain ⟨hdZ, -, hkZ, -, -, -⟩ := J.Iv.dZ_nonneg; positivity
  have hnW := J.nW_nonneg
  have hν := J.hν; have hδν := J.hδν
  have hKD : 0 ≤ J.KD := by unfold KD; positivity
  have hsM := Real.sqrt_nonneg J.M
  -- piece estimates
  have bCW := (J.CW_piece x yp).trans (show _ ≤ J.Iv.δCW * (J.X0 * ‖u‖) * (J.Py * ‖u‖ + J.Iv.δCW * (J.Y0 * ‖u‖))
      + (J.Px * ‖u‖) * (J.Iv.δCW * (J.Y0 * ‖u‖)) by gcongr)
  have bT := (J.T_piece x yp).trans (show _ ≤ J.Iv.Gm.dT * (J.X0 * ‖u‖) * (J.Py * ‖u‖ + J.Iv.Gm.dT * (J.Y0 * ‖u‖))
      + (J.Px * ‖u‖) * (J.Iv.Gm.dT * (J.Y0 * ‖u‖)) by gcongr)
  have bD := (J.Dp_piece x yp).trans (show _ ≤ J.KD * (J.X0 * ‖u‖) * (J.Y0 * ‖u‖) by gcongr)
  have bM0 := J.M_piece x yp
  have bM : J.M * |⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb yp⟫ - ⟪J.Qb x, J.Qb yp⟫|
      ≤ J.δB * (J.X0 * ‖u‖) * (Real.sqrt J.M * (J.Py * ‖u‖)) + J.M * J.δB ^ 2 * (J.X0 * ‖u‖) * (J.Y0 * ‖u‖)
        + Real.sqrt J.M * (J.Px * ‖u‖) * J.δB * (J.Y0 * ‖u‖) := by
    have e : J.M * (J.δB * ‖x‖ * (‖J.Qb yp‖ + J.δB * ‖yp‖) + ‖J.Qb x‖ * (J.δB * ‖yp‖))
        = J.δB * ‖x‖ * (Real.sqrt J.M * (Real.sqrt J.M * ‖J.Qb yp‖)) + J.M * J.δB ^ 2 * ‖x‖ * ‖yp‖
          + Real.sqrt J.M * (Real.sqrt J.M * ‖J.Qb x‖) * J.δB * ‖yp‖ := by
      have hs : Real.sqrt J.M * Real.sqrt J.M = J.M := Real.mul_self_sqrt hM
      linear_combination (-(J.δB * ‖x‖ * ‖J.Qb yp‖) - ‖J.Qb x‖ * J.δB * ‖yp‖) * hs
    refine (mul_le_mul_of_nonneg_left bM0 hM).trans ?_
    rw [e]
    gcongr
  -- assemble
  have hEN : J.EN * ‖u‖ ^ 2
      = J.δB * ‖u‖ * (J.Y0 * ‖u‖) + J.X0 * ‖u‖ * (J.δB * ‖u‖)
        + (J.Iv.δCW * (J.X0 * ‖u‖) * (J.Py * ‖u‖ + J.Iv.δCW * (J.Y0 * ‖u‖)) + (J.Px * ‖u‖) * (J.Iv.δCW * (J.Y0 * ‖u‖)))
        + J.KD * (J.X0 * ‖u‖) * (J.Y0 * ‖u‖)
        + (J.Iv.Gm.dT * (J.X0 * ‖u‖) * (J.Py * ‖u‖ + J.Iv.Gm.dT * (J.Y0 * ‖u‖)) + (J.Px * ‖u‖) * (J.Iv.Gm.dT * (J.Y0 * ‖u‖)))
        + (J.δB * (J.X0 * ‖u‖) * (Real.sqrt J.M * (J.Py * ‖u‖)) + J.M * J.δB ^ 2 * (J.X0 * ‖u‖) * (J.Y0 * ‖u‖)
          + Real.sqrt J.M * (J.Px * ‖u‖) * J.δB * (J.Y0 * ‖u‖)) := by
    unfold EN; ring
  have t1 : |⟪ap - a0, yp⟫| ≤ J.δB * ‖u‖ * (J.Y0 * ‖u‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hapd hyn (norm_nonneg _) (by positivity))
  have t2 : |⟪x, bp - a0⟫| ≤ J.X0 * ‖u‖ * (J.δB * ‖u‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hxn hbpd (norm_nonneg _) (by positivity))
  have hMabs : |J.M * (⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb yp⟫ - ⟪J.Qb x, J.Qb yp⟫)|
      = J.M * |⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb yp⟫ - ⟪J.Qb x, J.Qb yp⟫| := by
    rw [abs_mul, abs_of_nonneg hM]
  have h3abs : |⟪x, cjp J.ωE J.ωE J.Iv.Ginv yp⟫ - ⟪x, J.Iv.Ginv yp⟫|
      ≤ |⟪cjm J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) x, cjp J.ωE J.ωP (J.C ∘L J.Iv.Gm.W) yp⟫
          - ⟪J.C (J.Iv.Gm.W x), J.C (J.Iv.Gm.W yp)⟫|
        + |⟪cjm J.ωE J.ωE J.Iv.Gm.W x, cjp J.ωE J.ωE J.Dp (cjp J.ωE J.ωE J.Iv.Gm.W yp)⟫
          - ⟪J.Iv.Gm.W x, J.Dp (J.Iv.Gm.W yp)⟫|
        + |⟪cjm J.ωE J.ωS J.Iv.Gm.T x, cjp J.ωE J.ωS J.Iv.Gm.T yp⟫ - ⟪J.Iv.Gm.T x, J.Iv.Gm.T yp⟫|
        + J.M * |⟪cjm J.ωE J.ωB J.Qb x, cjp J.ωE J.ωB J.Qb yp⟫ - ⟪J.Qb x, J.Qb yp⟫| := by
    rw [hthird, ← hMabs]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have n1 := neg_abs_le ⟪ap - a0, yp⟫
  have n2 := neg_abs_le ⟪x, bp - a0⟫
  have n3 := le_abs_self (⟪x, cjp J.ωE J.ωE J.Iv.Ginv yp⟫ - ⟪x, J.Iv.Ginv yp⟫)
  rw [hNp, hN, hEN, hrep]
  linarith

theorem N_cjp_coer (u : B) : (1 / J.bN - J.EN) * ‖u‖ ^ 2 ≤ ⟪u, cjp J.ωB J.ωB J.N u⟫ := by
  have h1 := J.N_lower u
  have h2 := J.cjpN_lower u
  have hb := J.hbN
  have h3 : (1 / J.bN) * ‖u‖ ^ 2 ≤ ⟪u, J.N u⟫ := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]; linarith
  linarith

theorem Ninv_cjp (w : B) : (1 / J.bN - J.EN) * ‖cjp J.ωB J.ωB J.Ninv w‖ ≤ ‖w‖ :=
  inv_cjp_bound J.ωB J.N J.Ninv J.hN1 _ J.N_cjp_coer w

/-- **the weighted bound of `H = G Qb* N⁻¹`** -/
theorem H_cjp (hcN : 0 < 1 / J.bN - J.EN) (w : B) :
    ‖cjp J.ωB J.ωE J.H w‖ ≤ (2 / J.cg) * (J.qb + J.δB) / (1 / J.bN - J.EN) * ‖w‖ := by
  rw [cjpH_eq]
  simp only [ContinuousLinearMap.comp_apply]
  set v := cjp J.ωB J.ωB J.Ninv w
  have hcg := J.hcg
  have hv : ‖v‖ ≤ ‖w‖ / (1 / J.bN - J.EN) := by
    rw [le_div_iff₀ hcN]; linarith [J.Ninv_cjp w]
  have hq : ‖ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) v‖ ≤ (J.qb + J.δB) * ‖v‖ :=
    SiteHyp.norm_adj_sub_le _ _ J.cjmQb_norm v
  have hg := J.Gi_cjp (ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) v)
  have hg' : ‖cjp J.ωE J.ωE J.Gi (ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) v)‖
      ≤ (2 / J.cg) * ‖ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) v‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcg]; linarith
  have hqd : 0 ≤ J.qb + J.δB := by have := J.hqb; have := J.hδB; linarith
  calc _ ≤ (2 / J.cg) * ‖ContinuousLinearMap.adjoint (cjm J.ωE J.ωB J.Qb) v‖ := hg'
    _ ≤ (2 / J.cg) * ((J.qb + J.δB) * (‖w‖ / (1 / J.bN - J.EN))) := by
        gcongr
        exact hq.trans (mul_le_mul_of_nonneg_left hv hqd)
    _ = (2 / J.cg) * (J.qb + J.δB) / (1 / J.bN - J.EN) * ‖w‖ := by ring

end NHyp

#print axioms NHyp.cjpN_eq
#print axioms NHyp.cjpH_eq
#print axioms NHyp.cjpN_lower
#print axioms NHyp.N_cjp_coer
#print axioms NHyp.Ninv_cjp
#print axioms NHyp.H_cjp

end AdalyFormal.DLayer
