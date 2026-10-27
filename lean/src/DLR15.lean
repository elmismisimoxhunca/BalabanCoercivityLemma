import DLR14

/-!
# DL15 -- the gauge-fixing objects `T = R D*`, `Z = G' R D*`, `W = 1 − DZ` under the weights (abstract)

`T := D* − X Γ⁻¹ F*` (`F = DX`), `Z := G' T`, `W := 1 − D Z`.
* `T_diff` : `‖T⁺v − Tv‖ ≤ dT‖v‖`;  `Z_le` : `‖Z⁺v‖ ≤ kZ‖v‖`, `‖D Z⁺v‖ ≤ kDZ‖v‖`;
* `Z_diff` : `‖Z⁺v − Zv‖ ≤ dZ‖v‖`, `‖D(Z⁺v − Zv)‖ ≤ dDZ‖v‖`;  `W_diff` : `‖W⁺v − Wv‖ ≤ dW‖v‖`;  `W_le` : `‖Wv‖ ≤ (1+kDZ+dDZ)‖v‖`.
(All for `⁺`; the `⁻` versions are the same statements for `G` with inverted weights.)
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

noncomputable def T : E →L[ℝ] S := ContinuousLinearMap.adjoint G.D - G.H.X ∘L G.Gami ∘L ContinuousLinearMap.adjoint G.F
noncomputable def Z : E →L[ℝ] S := G.Linv ∘L G.T
noncomputable def W : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - G.D ∘L G.Z

theorem cjpT_eq : cjp G.ωE G.ωS G.T = ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D)
    - cjp G.ωY G.ωS G.H.X ∘L cjp G.ωY G.ωY G.Gami ∘L ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) := by
  rw [T, cjp_sub, cjp_comp G.ωE G.ωY G.ωS, cjp_comp G.ωE G.ωY G.ωY, adjoint_cjm, adjoint_cjm]

theorem cjpZ_eq : cjp G.ωE G.ωS G.Z = cjp G.ωS G.ωS G.Linv ∘L cjp G.ωE G.ωS G.T := by
  rw [Z, cjp_comp G.ωE G.ωS G.ωS]

theorem cjpW_eq : cjp G.ωE G.ωE G.W = ContinuousLinearMap.id ℝ E - cjp G.ωS G.ωE G.D ∘L cjp G.ωE G.ωS G.Z := by
  rw [W, cjp_sub, cjp_id, cjp_comp G.ωE G.ωS G.ωE]

theorem opnorm_of {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] (T : A →L[ℝ] B) (k : ℝ) (hk : 0 ≤ k) (h : ∀ v, ‖T v‖ ≤ k * ‖v‖) : ‖T‖ ≤ k :=
  ContinuousLinearMap.opNorm_le_bound _ hk h

theorem F_aux (v : E) :
    ‖ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v‖ ≤ G.kF * ‖v‖ ∧
    ‖ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v - ContinuousLinearMap.adjoint G.F v‖ ≤ G.dF * ‖v‖ := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := G.consts_nonneg
  have hk : ‖cjm G.ωY G.ωE G.F‖ ≤ G.kF := opnorm_of _ _ h2 (fun u => (G.cjmF_bounds u).1)
  have hd : ‖cjm G.ωY G.ωE G.F - G.F‖ ≤ G.dF := opnorm_of _ _ h3 (fun u => by
    rw [ContinuousLinearMap.sub_apply]; exact (G.cjmF_bounds u).2)
  refine ⟨SiteHyp.norm_adj_sub_le _ _ hk v, ?_⟩
  rw [← ContinuousLinearMap.sub_apply, ← map_sub]
  exact SiteHyp.norm_adj_sub_le _ _ hd v

theorem X_opnorm : ‖G.H.X‖ ≤ G.q / G.c :=
  opnorm_of _ _ (by have := G.hc; have := G.hq; positivity) (fun u => G.H.X_le G.q G.hQ u)

/-- the projection part `X Γ⁻¹ F*` and its weighted difference -/
theorem PD_bounds (v : E) :
    ‖cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami (ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v))‖
        ≤ G.nX * G.gi * G.kF * ‖v‖ ∧
    ‖cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami (ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v))
        - G.H.X (G.Gami (ContinuousLinearMap.adjoint G.F v))‖
        ≤ (G.H.epsX G.q * G.gi * G.kF + (G.q / G.c) * G.dGi * G.kF + (G.q / G.c) * G.gi * G.dF) * ‖v‖ := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := G.consts_nonneg
  obtain ⟨f1, f2⟩ := G.F_aux v
  set w' := ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v
  set w := ContinuousLinearMap.adjoint G.F v
  have hcG := G.hcG
  have g1 : ‖cjp G.ωY G.ωY G.Gami w'‖ ≤ G.gi * ‖w'‖ := by
    have := G.cjpGami_le w'; unfold gi; rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcG]; linarith
  have g2 : ‖G.Gami (w' - w)‖ ≤ G.gi * ‖w' - w‖ := by
    have := G.Gami_le (w' - w); unfold gi; rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcG]; linarith
  have hX := G.X_opnorm
  have heps := G.H.epsX_nonneg G.q G.hq
  have hqc : 0 ≤ G.q / G.c := by have := G.hc; have := G.hq; positivity
  refine ⟨?_, ?_⟩
  · refine ((G.cjX_le _).1).trans ?_
    calc G.nX * ‖cjp G.ωY G.ωY G.Gami w'‖ ≤ G.nX * (G.gi * (G.kF * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (g1.trans (mul_le_mul_of_nonneg_left f1 h4)) h0
      _ = G.nX * G.gi * G.kF * ‖v‖ := by ring
  · have e : cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami w') - G.H.X (G.Gami w)
        = (cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami w') - G.H.X (cjp G.ωY G.ωY G.Gami w'))
          + G.H.X (cjp G.ωY G.ωY G.Gami w' - G.Gami w') + G.H.X (G.Gami (w' - w)) := by
      rw [map_sub, map_sub, map_sub]; abel
    rw [e]
    have a1 : ‖cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami w') - G.H.X (cjp G.ωY G.ωY G.Gami w')‖
        ≤ G.H.epsX G.q * (G.gi * (G.kF * ‖v‖)) :=
      ((G.H.Xdiff G.q G.hq G.hQ _).1).trans
        (mul_le_mul_of_nonneg_left (g1.trans (mul_le_mul_of_nonneg_left f1 h4)) heps)
    have a2 : ‖G.H.X (cjp G.ωY G.ωY G.Gami w' - G.Gami w')‖ ≤ (G.q / G.c) * (G.dGi * (G.kF * ‖v‖)) :=
      (SiteHyp.norm_op_le _ _ hX _).trans (mul_le_mul_of_nonneg_left
        ((G.Gami_diff w').trans (mul_le_mul_of_nonneg_left f1 h5)) hqc)
    have a3 : ‖G.H.X (G.Gami (w' - w))‖ ≤ (G.q / G.c) * (G.gi * (G.dF * ‖v‖)) :=
      (SiteHyp.norm_op_le _ _ hX _).trans (mul_le_mul_of_nonneg_left
        (g2.trans (mul_le_mul_of_nonneg_left f2 h4)) hqc)
    have t1 := norm_add_le (cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami w') - G.H.X (cjp G.ωY G.ωY G.Gami w')
      + G.H.X (cjp G.ωY G.ωY G.Gami w' - G.Gami w')) (G.H.X (G.Gami (w' - w)))
    have t2 := norm_add_le (cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami w') - G.H.X (cjp G.ωY G.ωY G.Gami w'))
      (G.H.X (cjp G.ωY G.ωY G.Gami w' - G.Gami w'))
    nlinarith [norm_nonneg v]

theorem T_diff (v : E) : ‖cjp G.ωE G.ωS G.T v - G.T v‖ ≤ G.dT * ‖v‖ := by
  rw [cjpT_eq]
  obtain ⟨-, p2⟩ := G.PD_bounds v
  have hD : ‖ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v‖ ≤ G.δD * ‖v‖ := by
    rw [← ContinuousLinearMap.sub_apply, ← map_sub]; exact SiteHyp.norm_adj_sub_le _ _ G.hDm v
  have e : (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) - cjp G.ωY G.ωS G.H.X ∘L cjp G.ωY G.ωY G.Gami ∘L
        ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F)) v - G.T v
      = (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v)
        - (cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami (ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v))
          - G.H.X (G.Gami (ContinuousLinearMap.adjoint G.F v))) := by
    simp only [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  unfold dT
  nlinarith [norm_nonneg v]

theorem Z_le (v : E) : ‖cjp G.ωE G.ωS G.Z v‖ ≤ G.kZ * ‖v‖ ∧ ‖G.D (cjp G.ωE G.ωS G.Z v)‖ ≤ G.kDZ * ‖v‖ := by
  rw [cjpZ_eq, cjpT_eq]
  obtain ⟨p1, -⟩ := G.PD_bounds v
  obtain ⟨l1, l2⟩ := G.H.cjpLinvDadj_le v
  set y' := cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami (ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v))
  have e : (cjp G.ωS G.ωS G.Linv ∘L (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D)
        - cjp G.ωY G.ωS G.H.X ∘L cjp G.ωY G.ωY G.Gami ∘L ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F))) v
      = cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v) - cjp G.ωS G.ωS G.Linv y' := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    rfl
  rw [e]
  have hc := G.hc
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := G.consts_nonneg
  have b1 := (G.H.cjpLinv_le y').trans (mul_le_mul_of_nonneg_left p1 (by positivity))
  have b2 := (G.H.D_cjpLinv_le y').trans (mul_le_mul_of_nonneg_left p1 (Real.sqrt_nonneg _))
  refine ⟨(norm_sub_le _ _).trans ?_, ?_⟩
  · unfold kZ; nlinarith [norm_nonneg v]
  · rw [map_sub]; refine (norm_sub_le _ _).trans ?_
    unfold kDZ; nlinarith [norm_nonneg v]

theorem Z_diff (v : E) : ‖cjp G.ωE G.ωS G.Z v - G.Z v‖ ≤ G.dZ * ‖v‖ ∧
    ‖G.D (cjp G.ωE G.ωS G.Z v - G.Z v)‖ ≤ G.dDZ * ‖v‖ := by
  rw [cjpZ_eq, cjpT_eq]
  obtain ⟨p1, p2⟩ := G.PD_bounds v
  set y' := cjp G.ωY G.ωS G.H.X (cjp G.ωY G.ωY G.Gami (ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F) v))
  set y0 := G.H.X (G.Gami (ContinuousLinearMap.adjoint G.F v))
  set x1 := G.Linv (ContinuousLinearMap.adjoint G.D v)
  have eZ : G.Z v = x1 - G.Linv y0 := by
    simp only [Z, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]; rfl
  have e : (cjp G.ωS G.ωS G.Linv ∘L (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D)
        - cjp G.ωY G.ωS G.H.X ∘L cjp G.ωY G.ωY G.Gami ∘L ContinuousLinearMap.adjoint (cjm G.ωY G.ωE G.F))) v - G.Z v
      = (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v)
          + (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint G.D v) - x1))
        - ((cjp G.ωS G.ωS G.Linv y' - G.Linv y') + G.Linv (y' - y0)) := by
    rw [eZ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [e]
  have hc := G.hc
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := G.consts_nonneg
  have hδD := G.hδD
  have hK0 := G.H.K0_nonneg G.q G.hq
  have hK1 := G.H.K1_nonneg G.q G.hq
  have hsc : 0 < Real.sqrt G.c := Real.sqrt_pos.mpr hc
  have hDv : ‖ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v‖ ≤ G.δD * ‖v‖ := by
    rw [← ContinuousLinearMap.sub_apply, ← map_sub]; exact SiteHyp.norm_adj_sub_le _ _ G.hDm v
  obtain ⟨x1n, Dx1n⟩ := G.LinvDadj_unw v
  obtain ⟨r0, r1⟩ := G.H.resolvent_bound G.q G.hq G.hQ (ContinuousLinearMap.adjoint G.D v)
  obtain ⟨s0, s1⟩ := G.H.resolvent_bound G.q G.hq G.hQ y'
  obtain ⟨u0, u1⟩ := G.Linv_unw y'
  obtain ⟨w0, w1⟩ := G.Linv_unw (y' - y0)
  -- part 1
  have P1 : ‖cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v)
      + (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint G.D v) - x1)‖
      ≤ ((8 / G.c) * G.δD + G.H.K0 G.q / Real.sqrt G.c) * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    have a1 := (G.H.cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hDv (by positivity : (0:ℝ) ≤ 4 / G.c))
    have a2 : ‖cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint G.D v) - x1‖
        ≤ (4 / G.c) * G.δD * ‖v‖ + G.H.K0 G.q * (‖v‖ / Real.sqrt G.c) := by
      refine r0.trans ?_
      have := mul_le_mul_of_nonneg_left Dx1n (by positivity : (0:ℝ) ≤ 4 / G.c * G.δD)
      have := mul_le_mul_of_nonneg_left x1n hK0
      unfold SiteHyp.K0 at *
      linarith
    calc _ ≤ 4 / G.c * (G.δD * ‖v‖) + ((4 / G.c) * G.δD * ‖v‖ + G.H.K0 G.q * (‖v‖ / Real.sqrt G.c)) :=
          add_le_add a1 a2
      _ = ((8 / G.c) * G.δD + G.H.K0 G.q / Real.sqrt G.c) * ‖v‖ := by ring
  have P1D : ‖G.D (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint (cjm G.ωS G.ωE G.D) v - ContinuousLinearMap.adjoint G.D v)
      + (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint G.D v) - x1))‖
      ≤ (2 * Real.sqrt (12 / G.c) * G.δD + G.H.K1 G.q / Real.sqrt G.c) * ‖v‖ := by
    rw [map_add]; refine (norm_add_le _ _).trans ?_
    have a1 := (G.H.D_cjpLinv_le _).trans (mul_le_mul_of_nonneg_left hDv (Real.sqrt_nonneg _))
    have a2 : ‖G.D (cjp G.ωS G.ωS G.Linv (ContinuousLinearMap.adjoint G.D v) - x1)‖
        ≤ Real.sqrt (12 / G.c) * G.δD * ‖v‖ + G.H.K1 G.q * (‖v‖ / Real.sqrt G.c) := by
      refine r1.trans ?_
      have := mul_le_mul_of_nonneg_left Dx1n (by positivity : (0:ℝ) ≤ Real.sqrt (12 / G.c) * G.δD)
      have := mul_le_mul_of_nonneg_left x1n hK1
      unfold SiteHyp.K1 at *
      linarith
    calc _ ≤ Real.sqrt (12 / G.c) * (G.δD * ‖v‖)
          + (Real.sqrt (12 / G.c) * G.δD * ‖v‖ + G.H.K1 G.q * (‖v‖ / Real.sqrt G.c)) := add_le_add a1 a2
      _ = (2 * Real.sqrt (12 / G.c) * G.δD + G.H.K1 G.q / Real.sqrt G.c) * ‖v‖ := by ring
  -- part 2
  set A2 := G.H.epsX G.q * G.gi * G.kF + (G.q / G.c) * G.dGi * G.kF + (G.q / G.c) * G.gi * G.dF with hA2
  have hA20 : 0 ≤ A2 := by rw [hA2]; have := G.H.epsX_nonneg G.q G.hq; have := G.hq; positivity
  have P2 : ‖(cjp G.ωS G.ωS G.Linv y' - G.Linv y') + G.Linv (y' - y0)‖
      ≤ (((4 / G.c) * G.δD / Real.sqrt G.c + G.H.K0 G.q / G.c) * G.nX * G.gi * G.kF + (1 / G.c) * A2) * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    have a1 : ‖cjp G.ωS G.ωS G.Linv y' - G.Linv y'‖
        ≤ ((4 / G.c) * G.δD / Real.sqrt G.c + G.H.K0 G.q / G.c) * ‖y'‖ := by
      refine s0.trans ?_
      have := mul_le_mul_of_nonneg_left u1 (by positivity : (0:ℝ) ≤ 4 / G.c * G.δD)
      have := mul_le_mul_of_nonneg_left u0 hK0
      unfold SiteHyp.K0 at *
      have e3 : (4 / G.c) * G.δD / Real.sqrt G.c * ‖y'‖ = 4 / G.c * G.δD * (‖y'‖ / Real.sqrt G.c) := by ring
      have e4 : G.H.K0 G.q / G.c * ‖y'‖ = G.H.K0 G.q * (‖y'‖ / G.c) := by ring
      unfold SiteHyp.K0 at e4
      nlinarith
    have a2 : ‖G.Linv (y' - y0)‖ ≤ (1 / G.c) * (A2 * ‖v‖) := by
      refine w0.trans ?_
      rw [div_le_iff₀ hc]
      have : (1 / G.c) * (A2 * ‖v‖) * G.c = A2 * ‖v‖ := by field_simp
      rw [this]; exact p2
    have hc1 : 0 ≤ (4 / G.c) * G.δD / Real.sqrt G.c + G.H.K0 G.q / G.c := by positivity
    have a1' := a1.trans (mul_le_mul_of_nonneg_left p1 hc1)
    nlinarith [norm_nonneg v]
  have P2D : ‖G.D ((cjp G.ωS G.ωS G.Linv y' - G.Linv y') + G.Linv (y' - y0))‖
      ≤ ((Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 G.q / G.c) * G.nX * G.gi * G.kF
          + (1 / Real.sqrt G.c) * A2) * ‖v‖ := by
    rw [map_add]; refine (norm_add_le _ _).trans ?_
    have a1 : ‖G.D (cjp G.ωS G.ωS G.Linv y' - G.Linv y')‖
        ≤ (Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 G.q / G.c) * ‖y'‖ := by
      refine s1.trans ?_
      have := mul_le_mul_of_nonneg_left u1 (by positivity : (0:ℝ) ≤ Real.sqrt (12 / G.c) * G.δD)
      have := mul_le_mul_of_nonneg_left u0 hK1
      unfold SiteHyp.K1 at *
      have e3 : Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c * ‖y'‖
          = Real.sqrt (12 / G.c) * G.δD * (‖y'‖ / Real.sqrt G.c) := by ring
      have e4 : G.H.K1 G.q / G.c * ‖y'‖ = G.H.K1 G.q * (‖y'‖ / G.c) := by ring
      unfold SiteHyp.K1 at e4
      nlinarith
    have a2 : ‖G.D (G.Linv (y' - y0))‖ ≤ (1 / Real.sqrt G.c) * (A2 * ‖v‖) := by
      refine w1.trans ?_
      rw [div_le_iff₀ hsc]
      have : (1 / Real.sqrt G.c) * (A2 * ‖v‖) * Real.sqrt G.c = A2 * ‖v‖ := by field_simp
      rw [this]; exact p2
    have hc1 : 0 ≤ Real.sqrt (12 / G.c) * G.δD / Real.sqrt G.c + G.H.K1 G.q / G.c := by positivity
    have a1' := a1.trans (mul_le_mul_of_nonneg_left p1 hc1)
    nlinarith [norm_nonneg v]
  refine ⟨(norm_sub_le _ _).trans ?_, ?_⟩
  · unfold dZ; rw [hA2] at P2; nlinarith [norm_nonneg v]
  · rw [map_sub]; refine (norm_sub_le _ _).trans ?_
    unfold dDZ; rw [hA2] at P2D; nlinarith [norm_nonneg v]

theorem W_diff (v : E) : ‖cjp G.ωE G.ωE G.W v - G.W v‖ ≤ G.dW * ‖v‖ := by
  rw [cjpW_eq]
  obtain ⟨z1, -⟩ := G.Z_le v
  obtain ⟨-, z2⟩ := G.Z_diff v
  have e : (ContinuousLinearMap.id ℝ E - cjp G.ωS G.ωE G.D ∘L cjp G.ωE G.ωS G.Z) v - G.W v
      = -((cjp G.ωS G.ωE G.D - G.D) (cjp G.ωE G.ωS G.Z v) + G.D (cjp G.ωE G.ωS G.Z v - G.Z v)) := by
    simp only [W, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have a1 := (SiteHyp.norm_op_le _ _ G.hDp _).trans (mul_le_mul_of_nonneg_left z1 G.hδD)
  unfold dW; nlinarith [norm_nonneg v]

theorem W_le (v : E) : ‖G.W v‖ ≤ (1 + G.kDZ + G.dDZ) * ‖v‖ := by
  obtain ⟨-, z1⟩ := G.Z_le v
  obtain ⟨-, z2⟩ := G.Z_diff v
  have e : G.W v = v - (G.D (cjp G.ωE G.ωS G.Z v) - G.D (cjp G.ωE G.ωS G.Z v - G.Z v)) := by
    simp only [W, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_sub_le (G.D (cjp G.ωE G.ωS G.Z v)) (G.D (cjp G.ωE G.ωS G.Z v - G.Z v))
  nlinarith [norm_nonneg v]

end GamHyp

#print axioms GamHyp.cjpT_eq
#print axioms GamHyp.cjpZ_eq
#print axioms GamHyp.cjpW_eq
#print axioms GamHyp.F_aux
#print axioms GamHyp.PD_bounds
#print axioms GamHyp.T_diff
#print axioms GamHyp.Z_le
#print axioms GamHyp.Z_diff
#print axioms GamHyp.W_diff
#print axioms GamHyp.W_le

end AdalyFormal.DLayer
