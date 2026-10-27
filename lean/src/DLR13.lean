import DLR12

/-!
# DL13 -- `Γ⁻¹`, `T = R D*`, `Z = G' R D*`, `W = 1 − DZ` under the weights (abstract)

`GamHyp` = `SiteHyp` + `‖Qp‖ ≤ q`, a right inverse of `Qp` with `⟪g,Lg⟫ ≤ b‖u‖²`, a two-sided inverse `Gami` of `Γ = X*X`, and
`0 < cG ≤ 1/(2(qb)²) − 3 epsX²`.  With `R = 1 − X Γ⁻¹ X*` (the orthogonal projection onto `L·N(Qp)`, identified with the genuine
`Rproj` in the concrete instantiation):
* `cjpGam_coer`, `cjpGami_le` (`cG ‖(Γ⁻¹)⁺w‖ ≤ ‖w‖`), `Gami_le`, `Gami_diff` (`‖(Γ⁻¹)⁺w − Γ⁻¹w‖ ≤ dGi‖w‖`);
* `T_diff` : `‖T⁺v − Tv‖ ≤ dT‖v‖`;  `Z_le` : `‖Z⁺v‖ ≤ kZ‖v‖`, `‖DZ⁺v‖ ≤ kDZ‖v‖`;  `Z_diff` : `‖Z⁺v − Zv‖ ≤ dZ‖v‖`,
  `‖D(Z⁺v − Zv)‖ ≤ dDZ‖v‖`;  `W_diff` : `‖W⁺v − Wv‖ ≤ dW‖v‖`.  All constants are explicit `def`s.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

/-- the Γ-chain hypotheses -/
structure GamHyp (S E Y : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] extends SiteHyp S E Y where
  q : ℝ
  b : ℝ
  Gami : Y →L[ℝ] Y
  cG : ℝ
  hq : 0 ≤ q
  hb : 0 ≤ b
  hQ : ‖Qp‖ ≤ q
  ext : ∀ u : Y, ∃ g : S, Qp g = u ∧
    ⟪g, (ContinuousLinearMap.adjoint D ∘L D + m • (ContinuousLinearMap.adjoint Qp ∘L Qp)) g⟫ ≤ b * ‖u‖ ^ 2
  hG1 : ∀ u, (ContinuousLinearMap.adjoint (Linv ∘L ContinuousLinearMap.adjoint Qp) ∘L
    (Linv ∘L ContinuousLinearMap.adjoint Qp)) (Gami u) = u
  hG2 : ∀ u, Gami ((ContinuousLinearMap.adjoint (Linv ∘L ContinuousLinearMap.adjoint Qp) ∘L
    (Linv ∘L ContinuousLinearMap.adjoint Qp)) u) = u
  hcG : 0 < cG
  hcGdef : cG ≤ 1 / (2 * (q * b) ^ 2) - 3 * toSiteHyp.epsX q ^ 2

namespace GamHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (G : GamHyp S E Y)

/-- abbreviations -/
noncomputable abbrev H : SiteHyp S E Y := G.toSiteHyp

theorem Gam_eq : G.H.Gam = ContinuousLinearMap.adjoint (G.Linv ∘L ContinuousLinearMap.adjoint G.Qp) ∘L
    (G.Linv ∘L ContinuousLinearMap.adjoint G.Qp) := rfl

theorem Gam_Gami (u : Y) : G.H.Gam (G.Gami u) = u := G.hG1 u
theorem Gami_Gam (u : Y) : G.Gami (G.H.Gam u) = u := G.hG2 u

theorem Gam_form (u : Y) : ⟪u, G.H.Gam u⟫ = ‖G.H.X u‖ ^ 2 := by
  rw [SiteHyp.Gam, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem qb_X (u : Y) : ‖u‖ ≤ G.q * G.b * ‖G.H.X u‖ :=
  G.H.gamma_lower G.q G.b G.hq G.hb G.hQ G.ext u

theorem cjpGam_coer (u : Y) : G.cG * ‖u‖ ^ 2 ≤ ⟪u, cjp G.ωY G.ωY G.H.Gam u⟫ := by
  have h1 := G.H.gamma_cjp_lower G.q G.hq G.hQ u
  have h2 := G.qb_X u
  have hc := G.hcGdef
  have hcG := G.hcG
  by_cases hqb : G.q * G.b = 0
  · rw [hqb, zero_mul] at h2
    have hu : ‖u‖ = 0 := le_antisymm h2 (norm_nonneg _)
    rw [hu]
    have := G.H.gamma_cjp_lower G.q G.hq G.hQ u
    rw [hu] at this
    nlinarith [sq_nonneg ‖G.H.X u‖]
  have hqb' : 0 < G.q * G.b := lt_of_le_of_ne (mul_nonneg G.hq G.hb) (Ne.symm hqb)
  have h3 : ‖u‖ ^ 2 / (G.q * G.b) ^ 2 ≤ ‖G.H.X u‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith
  have h4 : (1 / (2 * (G.q * G.b) ^ 2)) * ‖u‖ ^ 2 = (1 / 2) * (‖u‖ ^ 2 / (G.q * G.b) ^ 2) := by
    field_simp
  have h5 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖)
  nlinarith

theorem cjpGami_le (w : Y) : G.cG * ‖cjp G.ωY G.ωY G.Gami w‖ ≤ ‖w‖ :=
  inv_cjp_bound G.ωY G.H.Gam G.Gami (fun x => G.Gam_Gami x) G.cG (fun h => G.cjpGam_coer h) w

theorem Gam_coer (u : Y) : G.cG * ‖u‖ ^ 2 ≤ ⟪u, G.H.Gam u⟫ := by
  rw [Gam_form]
  have h2 := G.qb_X u
  have hc := G.hcGdef
  have hcG := G.hcG
  have heps := sq_nonneg (G.H.epsX G.q)
  by_cases hqb : G.q * G.b = 0
  · rw [hqb, zero_mul] at h2
    have hu : ‖u‖ = 0 := le_antisymm h2 (norm_nonneg _)
    rw [hu]; nlinarith [sq_nonneg ‖G.H.X u‖]
  have hqb' : 0 < G.q * G.b := lt_of_le_of_ne (mul_nonneg G.hq G.hb) (Ne.symm hqb)
  have h3 : ‖u‖ ^ 2 / (G.q * G.b) ^ 2 ≤ ‖G.H.X u‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith
  have h4 : G.cG ≤ 1 / (G.q * G.b) ^ 2 := by
    have : 1 / (2 * (G.q * G.b) ^ 2) ≤ 1 / (G.q * G.b) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [sq_nonneg (G.q * G.b)]
    linarith
  have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖u‖)
  have h6 : 1 / (G.q * G.b) ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 2 / (G.q * G.b) ^ 2 := by ring
  linarith

theorem Gami_le (w : Y) : G.cG * ‖G.Gami w‖ ≤ ‖w‖ := by
  have h := inv_cjp_bound (WPair.one Y) G.H.Gam G.Gami (fun x => G.Gam_Gami x) G.cG
    (fun h => by rw [cjp_one]; exact G.Gam_coer h) w
  rwa [cjp_one] at h

/-- `dΓ = 2 epsX (q/c) + epsX²` bounds `Γ − Γ⁺` -/
noncomputable def dGam : ℝ := 2 * G.H.epsX G.q * (G.q / G.c) + G.H.epsX G.q ^ 2

theorem cjpGam_eq : cjp G.ωY G.ωY G.H.Gam = ContinuousLinearMap.adjoint (cjm G.ωY G.ωS G.H.X) ∘L cjp G.ωY G.ωS G.H.X := by
  rw [SiteHyp.Gam, cjp_comp G.ωY G.ωS G.ωY, adjoint_cjm]

theorem Gam_sub_le (u : Y) : ‖G.H.Gam u - cjp G.ωY G.ωY G.H.Gam u‖ ≤ G.dGam * ‖u‖ := by
  rw [cjpGam_eq]
  set X := G.H.X
  set Xp := cjp G.ωY G.ωS X
  set Xm := cjm G.ωY G.ωS X
  have e : G.H.Gam u - (ContinuousLinearMap.adjoint Xm ∘L Xp) u
      = -(ContinuousLinearMap.adjoint (Xm - X) (X u) + ContinuousLinearMap.adjoint X ((Xp - X) u)
          + ContinuousLinearMap.adjoint (Xm - X) ((Xp - X) u)) := by
    simp only [SiteHyp.Gam, ContinuousLinearMap.comp_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [e, norm_neg]
  have heps := G.H.epsX_nonneg G.q G.hq
  have hXp : ‖Xp - X‖ ≤ G.H.epsX G.q := by
    refine ContinuousLinearMap.opNorm_le_bound _ heps (fun u => ?_)
    rw [ContinuousLinearMap.sub_apply]; exact (G.H.Xdiff G.q G.hq G.hQ u).1
  have hXm : ‖Xm - X‖ ≤ G.H.epsX G.q := by
    refine ContinuousLinearMap.opNorm_le_bound _ heps (fun u => ?_)
    rw [ContinuousLinearMap.sub_apply]; exact (G.H.Xdiff_m G.q G.hq G.hQ u).1
  have hX : ‖X‖ ≤ G.q / G.c := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by have := G.hc; have := G.hq; positivity) (fun u => ?_)
    exact G.H.X_le G.q G.hQ u
  have a1 := SiteHyp.norm_adj_sub_le (Xm - X) _ hXm (X u)
  have a2 := SiteHyp.norm_adj_sub_le X _ hX ((Xp - X) u)
  have a3 := SiteHyp.norm_adj_sub_le (Xm - X) _ hXm ((Xp - X) u)
  have b1 := SiteHyp.norm_op_le X _ hX u
  have b2 := SiteHyp.norm_op_le (Xp - X) _ hXp u
  have hqc : 0 ≤ G.q / G.c := by have := G.hc; have := G.hq; positivity
  have c1 := mul_le_mul_of_nonneg_left b1 heps
  have c2 := mul_le_mul_of_nonneg_left b2 hqc
  have c3 := mul_le_mul_of_nonneg_left b2 heps
  have t := norm_add_le (ContinuousLinearMap.adjoint (Xm - X) (X u) + ContinuousLinearMap.adjoint X ((Xp - X) u))
    (ContinuousLinearMap.adjoint (Xm - X) ((Xp - X) u))
  have t2 := norm_add_le (ContinuousLinearMap.adjoint (Xm - X) (X u)) (ContinuousLinearMap.adjoint X ((Xp - X) u))
  unfold dGam
  nlinarith [norm_nonneg u]

/-- `‖(Γ⁻¹)⁺w − Γ⁻¹w‖ ≤ dGi‖w‖`, `dGi = dΓ/cG²` -/
noncomputable def dGi : ℝ := G.dGam / G.cG ^ 2

theorem Gami_diff (w : Y) : ‖cjp G.ωY G.ωY G.Gami w - G.Gami w‖ ≤ G.dGi * ‖w‖ := by
  have hres : cjp G.ωY G.ωY G.Gami w - G.Gami w
      = cjp G.ωY G.ωY G.Gami ((G.H.Gam - cjp G.ωY G.ωY G.H.Gam) (G.Gami w)) := by
    rw [ContinuousLinearMap.sub_apply, map_sub, G.Gam_Gami]
    have : cjp G.ωY G.ωY G.Gami (cjp G.ωY G.ωY G.H.Gam (G.Gami w)) = G.Gami w := by
      rw [cjp_apply, cjp_apply, G.ωY.wi_w, G.Gami_Gam, G.ωY.w_wi]
    rw [this]
  rw [hres]
  have hcG := G.hcG
  have h1 := G.cjpGami_le ((G.H.Gam - cjp G.ωY G.ωY G.H.Gam) (G.Gami w))
  have h2 : ‖(G.H.Gam - cjp G.ωY G.ωY G.H.Gam) (G.Gami w)‖ ≤ G.dGam * ‖G.Gami w‖ := by
    rw [ContinuousLinearMap.sub_apply]; exact G.Gam_sub_le _
  have h3 := G.Gami_le w
  have hd : 0 ≤ G.dGam := by
    unfold dGam; have := G.H.epsX_nonneg G.q G.hq; have := G.hc; have := G.hq; positivity
  have h4 : ‖G.Gami w‖ ≤ ‖w‖ / G.cG := by rw [le_div_iff₀ hcG]; linarith
  have h5 : ‖cjp G.ωY G.ωY G.Gami ((G.H.Gam - cjp G.ωY G.ωY G.H.Gam) (G.Gami w))‖
      ≤ (G.dGam * ‖G.Gami w‖) / G.cG := by
    rw [le_div_iff₀ hcG]; linarith
  calc _ ≤ (G.dGam * ‖G.Gami w‖) / G.cG := h5
    _ ≤ (G.dGam * (‖w‖ / G.cG)) / G.cG := by
        apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hd) hcG.le
    _ = G.dGi * ‖w‖ := by unfold dGi; field_simp

end GamHyp

#print axioms GamHyp.Gam_form
#print axioms GamHyp.qb_X
#print axioms GamHyp.cjpGam_coer
#print axioms GamHyp.cjpGami_le
#print axioms GamHyp.Gam_coer
#print axioms GamHyp.Gami_le
#print axioms GamHyp.cjpGam_eq
#print axioms GamHyp.Gam_sub_le
#print axioms GamHyp.Gami_diff

end AdalyFormal.DLayer
