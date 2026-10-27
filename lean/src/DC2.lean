import DLR9

/-!
# DC2 -- the WEIGHTED Schur complement `N = Q G Q*` and `H = G Q* N⁻¹` under a Combes–Thomas weight (abstract)

The stratified analogue of DL18–DL20 with the coercivity of `G⁻¹` only in a WEIGHTED norm (`cw ‖Nw f‖² ≤ ⟪f, G⁻¹ f⟫`, the M1
node W4) and every Combes–Thomas error measured FORM-relatively.  Hilbert-space level (Mathlib + DL9 `WPair`, `cjp`, `cjm`).

`WSchur E F`: `G⁻¹` symmetric with two-sided inverse `Gi`; `Q : E → F`; `N⁻¹` two-sided inverse of `N = Q Gi Q*`; CT weights
`ωE, ωF`; a norm operator `Nw` on `E`; a row weight pair `Mw` on `F` (`Mw.w = M⁻¹`, `Mw.wi = M`); hypotheses
* `hcoer` : `cw ‖Nw f‖² ≤ ⟪f, G⁻¹ f⟫` (W4);
* `hHB`   : `|⟪x, (G⁻¹)⁺ y⟫ − ⟪x, G⁻¹ y⟫| ≤ κ √⟪x,G⁻¹x⟫ √⟪y,G⁻¹y⟫` (the form-relative CT of `G⁻¹`), `κ < 1`;
* `hQ`    : `‖M⁻¹ Q h‖ ≤ CQ √⟪h,G⁻¹h⟫` (the mass term);  `hQp`, `hQm` : `‖M⁻¹ (Q^± − Q) h‖ ≤ dB ‖Nw h‖`;
* `hext`  : every `v` has a preimage `Q g = v` with `⟪g, G⁻¹ g⟫ ≤ bN ‖M⁻¹ v‖²` (the bond right inverse, M1 node W6).
Outputs:
* `N_lower` : `‖M u‖² ≤ bN ⟪u, N u⟫`;  `cjpN_lower` : `⟪u,N⁺u⟫ ≥ ⟪u,Nu⟫ − EN ‖M u‖²`;
* `Ninv_cjp` : `cN ‖M (N⁻¹)⁺ w‖ ≤ ‖M⁻¹ w‖` (`cN = 1/bN − EN > 0`);
* **`H_cjp_w`** : `‖Nw H⁺ w‖ ≤ CHw · ‖M⁻¹ w‖`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.DLayer

structure WSchur (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F] where
  Ginv : E →L[ℝ] E
  Gi : E →L[ℝ] E
  Q : E →L[ℝ] F
  Ninv : F →L[ℝ] F
  ωE : WPair E
  ωF : WPair F
  Nw : E →L[ℝ] E
  Mw : WPair F
  cw : ℝ
  κ : ℝ
  CQ : ℝ
  dB : ℝ
  bN : ℝ
  hcw : 0 < cw
  hκ0 : 0 ≤ κ
  hκ1 : κ < 1
  hCQ : 0 ≤ CQ
  hdB : 0 ≤ dB
  hbN : 0 < bN
  hsym : ∀ x y, ⟪Ginv x, y⟫ = ⟪x, Ginv y⟫
  hGi1 : ∀ x, Ginv (Gi x) = x
  hGi2 : ∀ x, Gi (Ginv x) = x
  hcoer : ∀ f, cw * ‖Nw f‖ ^ 2 ≤ ⟪f, Ginv f⟫
  hHB : ∀ x y, |⟪x, cjp ωE ωE Ginv y⟫ - ⟪x, Ginv y⟫| ≤ κ * (Real.sqrt ⟪x, Ginv x⟫ * Real.sqrt ⟪y, Ginv y⟫)
  hQ : ∀ h, ‖Mw.w (Q h)‖ ≤ CQ * Real.sqrt ⟪h, Ginv h⟫
  hQp : ∀ h, ‖Mw.w ((cjp ωE ωF Q - Q) h)‖ ≤ dB * ‖Nw h‖
  hQm : ∀ h, ‖Mw.w ((cjm ωE ωF Q - Q) h)‖ ≤ dB * ‖Nw h‖
  hext : ∀ v : F, ∃ g : E, Q g = v ∧ ⟪g, Ginv g⟫ ≤ bN * ‖Mw.w v‖ ^ 2
  hN1 : ∀ u, (Q ∘L Gi ∘L ContinuousLinearMap.adjoint Q) (Ninv u) = u
  hN2 : ∀ u, Ninv ((Q ∘L Gi ∘L ContinuousLinearMap.adjoint Q) u) = u

namespace WSchur

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
variable (J : WSchur E F)

noncomputable def N : F →L[ℝ] F := J.Q ∘L J.Gi ∘L ContinuousLinearMap.adjoint J.Q
noncomputable def H : F →L[ℝ] E := J.Gi ∘L ContinuousLinearMap.adjoint J.Q ∘L J.Ninv

/-- the energy -/
noncomputable def En (h : E) : ℝ := ⟪h, J.Ginv h⟫

theorem En_nonneg (h : E) : 0 ≤ J.En h :=
  le_trans (by have := J.hcw; positivity) (J.hcoer h)

theorem Nw_le (h : E) : ‖J.Nw h‖ ≤ Real.sqrt (J.En h) / Real.sqrt J.cw := by
  rw [le_div_iff₀ (Real.sqrt_pos.mpr J.hcw), ← Real.sqrt_sq (norm_nonneg (J.Nw h)), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (by rw [mul_comm]; exact J.hcoer h)

/-- `⟪u, Mw u'⟫` splitting -/
theorem pair_M (z y : F) : ⟪z, y⟫ ≤ ‖J.Mw.w z‖ * ‖J.Mw.wi y‖ := by
  have e : ⟪z, y⟫ = ⟪J.Mw.w z, J.Mw.wi y⟫ := by rw [J.Mw.w_sym, J.Mw.w_wi]
  rw [e]; exact real_inner_le_norm _ _

theorem abs_pair_M (u z : F) : |⟪u, z⟫| ≤ ‖J.Mw.wi u‖ * ‖J.Mw.w z‖ := by
  have e : ⟪u, z⟫ = ⟪J.Mw.wi u, J.Mw.w z⟫ := by rw [← J.Mw.w_sym, J.Mw.w_wi]
  rw [e]; exact abs_real_inner_le_norm _ _

theorem cjpGinv_Gi (x : E) : cjp J.ωE J.ωE J.Ginv (cjp J.ωE J.ωE J.Gi x) = x := by
  rw [cjp_apply, cjp_apply, J.ωE.wi_w, J.hGi1, J.ωE.w_wi]

/-- `⟪y,(G⁻¹)⁺y⟫ ≥ (1−κ) E(y)` -/
theorem cjp_form_lower (y : E) : (1 - J.κ) * J.En y ≤ ⟪y, cjp J.ωE J.ωE J.Ginv y⟫ := by
  have h := J.hHB y y
  have hE := J.En_nonneg y
  have hs : Real.sqrt ⟪y, J.Ginv y⟫ * Real.sqrt ⟪y, J.Ginv y⟫ = J.En y := Real.mul_self_sqrt hE
  rw [hs] at h
  have := (abs_le.mp h).1
  unfold En at *
  nlinarith

/-- an energy bound from a pairing with a `Q`-image: if `⟪h,(G⁻¹)⁺h⟫ = ⟪Q⁻ h, y⟫` then `√E(h) ≤ Cy ‖M y‖`. -/
noncomputable def Cy : ℝ := (J.CQ + J.dB / Real.sqrt J.cw) / (1 - J.κ)

theorem Cy_nonneg : 0 ≤ J.Cy := by
  unfold Cy
  have := J.hκ1; have := J.hCQ; have := J.hdB; have := J.hcw
  have : 0 < 1 - J.κ := by linarith
  positivity

theorem sqrtE_of_pair (h : E) (y : F) (hp : ⟪h, cjp J.ωE J.ωE J.Ginv h⟫ = ⟪cjm J.ωE J.ωF J.Q h, y⟫) :
    Real.sqrt (J.En h) ≤ J.Cy * ‖J.Mw.wi y‖ := by
  have hE := J.En_nonneg h
  have h1 := J.cjp_form_lower h
  rw [hp] at h1
  have h2 := J.pair_M (cjm J.ωE J.ωF J.Q h) y
  have h3 : ‖J.Mw.w (cjm J.ωE J.ωF J.Q h)‖ ≤ (J.CQ + J.dB / Real.sqrt J.cw) * Real.sqrt (J.En h) := by
    have e : cjm J.ωE J.ωF J.Q h = J.Q h + (cjm J.ωE J.ωF J.Q - J.Q) h := by
      rw [ContinuousLinearMap.sub_apply]; abel
    rw [e, map_add]
    refine (norm_add_le _ _).trans ?_
    have a : ‖J.Mw.w (J.Q h)‖ ≤ J.CQ * Real.sqrt (J.En h) := J.hQ h
    have b : ‖J.Mw.w ((cjm J.ωE J.ωF J.Q - J.Q) h)‖ ≤ (J.dB / Real.sqrt J.cw) * Real.sqrt (J.En h) := by
      have := (J.hQm h).trans (mul_le_mul_of_nonneg_left (J.Nw_le h) J.hdB)
      calc _ ≤ _ := this
        _ = (J.dB / Real.sqrt J.cw) * Real.sqrt (J.En h) := by ring
    calc _ ≤ J.CQ * Real.sqrt (J.En h) + (J.dB / Real.sqrt J.cw) * Real.sqrt (J.En h) := add_le_add a b
      _ = _ := by ring
  have hk : 0 < 1 - J.κ := by linarith [J.hκ1]
  have hs : Real.sqrt (J.En h) * Real.sqrt (J.En h) = J.En h := Real.mul_self_sqrt hE
  have hsq0 := Real.sqrt_nonneg (J.En h)
  have hMy := norm_nonneg (J.Mw.wi y)
  have h4 : (1 - J.κ) * (Real.sqrt (J.En h) * Real.sqrt (J.En h))
      ≤ ((J.CQ + J.dB / Real.sqrt J.cw) * Real.sqrt (J.En h)) * ‖J.Mw.wi y‖ := by
    rw [hs]; exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 hMy))
  by_cases h0 : Real.sqrt (J.En h) = 0
  · rw [h0]; exact mul_nonneg J.Cy_nonneg hMy
  have hpos : 0 < Real.sqrt (J.En h) := lt_of_le_of_ne hsq0 (Ne.symm h0)
  have h5 : (1 - J.κ) * Real.sqrt (J.En h) ≤ (J.CQ + J.dB / Real.sqrt J.cw) * ‖J.Mw.wi y‖ := by
    have : (1 - J.κ) * Real.sqrt (J.En h) * Real.sqrt (J.En h)
        ≤ (J.CQ + J.dB / Real.sqrt J.cw) * ‖J.Mw.wi y‖ * Real.sqrt (J.En h) := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  unfold Cy
  rw [div_mul_eq_mul_div, le_div_iff₀ hk]
  linarith

/-- **the weighted lower bound of `N`** (only the competitor energy) -/
theorem N_lower (u : F) : ‖J.Mw.wi u‖ ^ 2 ≤ J.bN * ⟪u, J.N u⟫ := by
  obtain ⟨g, hg, hgE⟩ := J.hext (J.Mw.wi (J.Mw.wi u))
  set x := J.Gi (ContinuousLinearMap.adjoint J.Q u) with hx
  have hGx : J.Ginv x = ContinuousLinearMap.adjoint J.Q u := J.hGi1 _
  have hNu : ⟪u, J.N u⟫ = ⟪x, J.Ginv x⟫ := by
    rw [hGx, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]; rfl
  have e1 : ‖J.Mw.wi u‖ ^ 2 = ⟪x, J.Ginv g⟫ := by
    rw [← J.hsym, hGx, ContinuousLinearMap.adjoint_inner_left, hg, ← J.Mw.wi_sym, real_inner_self_eq_norm_sq]
  have hpos : ∀ y, 0 ≤ ⟪y, J.Ginv y⟫ := fun y => J.En_nonneg y
  have hgE' : ⟪g, J.Ginv g⟫ ≤ J.bN * ‖J.Mw.wi u‖ ^ 2 := by
    rw [J.Mw.w_wi] at hgE; exact hgE
  -- Cauchy–Schwarz in the G⁻¹ form
  have hCS : ⟪x, J.Ginv g⟫ ^ 2 ≤ ⟪x, J.Ginv x⟫ * ⟪g, J.Ginv g⟫ := by
    have hq' : ∀ t : ℝ, 0 ≤ ⟪x, J.Ginv x⟫ + 2 * t * ⟪x, J.Ginv g⟫ + t ^ 2 * ⟪g, J.Ginv g⟫ := by
      intro t
      have := hpos (x + t • g)
      have e : ⟪x + t • g, J.Ginv (x + t • g)⟫
          = ⟪x, J.Ginv x⟫ + 2 * t * ⟪x, J.Ginv g⟫ + t ^ 2 * ⟪g, J.Ginv g⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        have : ⟪g, J.Ginv x⟫ = ⟪x, J.Ginv g⟫ := by rw [← J.hsym, real_inner_comm]
        rw [this]; ring
      rw [e] at this; exact this
    by_cases hg0 : ⟪g, J.Ginv g⟫ = 0
    · have hx0 : ⟪x, J.Ginv g⟫ = 0 := by
        by_contra hne
        have ht := hq' (-(⟪x, J.Ginv x⟫ + 1) / (2 * ⟪x, J.Ginv g⟫))
        have e : 2 * (-(⟪x, J.Ginv x⟫ + 1) / (2 * ⟪x, J.Ginv g⟫)) * ⟪x, J.Ginv g⟫ = -(⟪x, J.Ginv x⟫ + 1) := by
          field_simp
        rw [hg0, e] at ht
        linarith [ht, mul_zero ((-(⟪x, J.Ginv x⟫ + 1) / (2 * ⟪x, J.Ginv g⟫)) ^ 2)]
      rw [hx0, hg0]; simp
    · have hgpos : 0 < ⟪g, J.Ginv g⟫ := lt_of_le_of_ne (hpos g) (Ne.symm hg0)
      have := hq' (-⟪x, J.Ginv g⟫ / ⟪g, J.Ginv g⟫)
      have e : ⟪x, J.Ginv x⟫ + 2 * (-⟪x, J.Ginv g⟫ / ⟪g, J.Ginv g⟫) * ⟪x, J.Ginv g⟫
          + (-⟪x, J.Ginv g⟫ / ⟪g, J.Ginv g⟫) ^ 2 * ⟪g, J.Ginv g⟫
          = ⟪x, J.Ginv x⟫ - ⟪x, J.Ginv g⟫ ^ 2 / ⟪g, J.Ginv g⟫ := by field_simp; ring
      rw [e] at this
      have h2 : ⟪x, J.Ginv g⟫ ^ 2 / ⟪g, J.Ginv g⟫ ≤ ⟪x, J.Ginv x⟫ := by linarith
      rwa [div_le_iff₀ hgpos] at h2
  have h4 : (‖J.Mw.wi u‖ ^ 2) ^ 2 ≤ ⟪x, J.Ginv x⟫ * (J.bN * ‖J.Mw.wi u‖ ^ 2) := by
    calc (‖J.Mw.wi u‖ ^ 2) ^ 2 = ⟪x, J.Ginv g⟫ ^ 2 := by rw [e1]
      _ ≤ ⟪x, J.Ginv x⟫ * ⟪g, J.Ginv g⟫ := hCS
      _ ≤ ⟪x, J.Ginv x⟫ * (J.bN * ‖J.Mw.wi u‖ ^ 2) := mul_le_mul_of_nonneg_left hgE' (hpos x)
  rw [hNu]
  by_cases hu : ‖J.Mw.wi u‖ ^ 2 = 0
  · rw [hu]; exact mul_nonneg J.hbN.le (hpos x)
  have hu2 : 0 < ‖J.Mw.wi u‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hu)
  nlinarith

theorem cjpN_eq : cjp J.ωF J.ωF J.N
    = cjp J.ωE J.ωF J.Q ∘L cjp J.ωE J.ωE J.Gi ∘L ContinuousLinearMap.adjoint (cjm J.ωE J.ωF J.Q) := by
  unfold N
  rw [cjp_comp J.ωF J.ωE J.ωF, cjp_comp J.ωF J.ωE J.ωE, adjoint_cjm]

/-- the CT error of `N` -/
noncomputable def EN : ℝ :=
  J.dB * (J.Cy / Real.sqrt J.cw) + J.dB * (J.CQ / Real.sqrt J.cw) + J.κ * (J.CQ * J.Cy)

theorem EN_nonneg : 0 ≤ J.EN := by
  unfold EN; have := J.Cy_nonneg; have := J.hdB; have := J.hCQ; have := J.hκ0; have := J.hcw; positivity

/-- **`⟪u,N⁺u⟫ ≥ ⟪u,Nu⟫ − EN ‖M u‖²`** -/
theorem cjpN_lower (u : F) : ⟪u, J.N u⟫ - J.EN * ‖J.Mw.wi u‖ ^ 2 ≤ ⟪u, cjp J.ωF J.ωF J.N u⟫ := by
  set a0 := ContinuousLinearMap.adjoint J.Q u with ha0
  set x := J.Gi a0 with hxdef
  set bp := ContinuousLinearMap.adjoint (cjm J.ωE J.ωF J.Q) u with hbp
  set ap := ContinuousLinearMap.adjoint (cjp J.ωE J.ωF J.Q) u with hap
  set yp := cjp J.ωE J.ωE J.Gi bp with hyp
  have hNp : ⟪u, cjp J.ωF J.ωF J.N u⟫ = ⟪ap, yp⟫ := by
    rw [cjpN_eq]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left]
  have hN : ⟪u, J.N u⟫ = ⟪a0, x⟫ := by
    show ⟪u, J.Q (J.Gi (ContinuousLinearMap.adjoint J.Q u))⟫ = _
    rw [← ContinuousLinearMap.adjoint_inner_left]
  have hx : J.Ginv x = a0 := J.hGi1 a0
  have hy : cjp J.ωE J.ωE J.Ginv yp = bp := J.cjpGinv_Gi bp
  have h1 : ⟪a0, yp⟫ = ⟪x, J.Ginv yp⟫ := by rw [← hx, J.hsym]
  have h2 : ⟪x, bp⟫ = ⟪x, cjp J.ωE J.ωE J.Ginv yp⟫ := by rw [hy]
  have h3 : ⟪x, a0⟫ = ⟪a0, x⟫ := real_inner_comm _ _
  have hrep : ⟪ap, yp⟫ = ⟪a0, x⟫ + ⟪ap - a0, yp⟫ + ⟪x, bp - a0⟫
      - (⟪x, cjp J.ωE J.ωE J.Ginv yp⟫ - ⟪x, J.Ginv yp⟫) := by
    rw [inner_sub_left, inner_sub_right]; linarith
  -- energies of `x` and `y⁺`
  have hEx : Real.sqrt (J.En x) ≤ J.CQ * ‖J.Mw.wi u‖ := by
    have hE := J.En_nonneg x
    have e : J.En x = ⟪J.Q x, u⟫ := by
      unfold En; rw [hx, ha0, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    have h4 := (J.pair_M (J.Q x) u).trans (mul_le_mul_of_nonneg_right (J.hQ x) (norm_nonneg _))
    rw [← e] at h4
    have hs : Real.sqrt (J.En x) * Real.sqrt (J.En x) = J.En x := Real.mul_self_sqrt hE
    have hsq0 := Real.sqrt_nonneg (J.En x)
    by_cases h0 : Real.sqrt (J.En x) = 0
    · rw [h0]; exact mul_nonneg J.hCQ (norm_nonneg _)
    have hpos : 0 < Real.sqrt (J.En x) := lt_of_le_of_ne hsq0 (Ne.symm h0)
    have : Real.sqrt (J.En x) * Real.sqrt (J.En x) ≤ J.CQ * ‖J.Mw.wi u‖ * Real.sqrt (J.En x) := by
      unfold En at *; nlinarith
    exact le_of_mul_le_mul_right this hpos
  have hEy : Real.sqrt (J.En yp) ≤ J.Cy * ‖J.Mw.wi u‖ := by
    refine J.sqrtE_of_pair yp u ?_
    rw [hy, hbp, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  -- the three brackets
  have k1 : |⟪ap - a0, yp⟫| ≤ ‖J.Mw.wi u‖ * (J.dB * ‖J.Nw yp‖) := by
    have e : ap - a0 = ContinuousLinearMap.adjoint (cjp J.ωE J.ωF J.Q - J.Q) u := by
      rw [hap, ha0, map_sub, ContinuousLinearMap.sub_apply]
    rw [e, ContinuousLinearMap.adjoint_inner_left]
    exact (J.abs_pair_M u _).trans (mul_le_mul_of_nonneg_left (J.hQp yp) (norm_nonneg _))
  have k2 : |⟪x, bp - a0⟫| ≤ ‖J.Mw.wi u‖ * (J.dB * ‖J.Nw x‖) := by
    have e : bp - a0 = ContinuousLinearMap.adjoint (cjm J.ωE J.ωF J.Q - J.Q) u := by
      rw [hbp, ha0, map_sub, ContinuousLinearMap.sub_apply]
    rw [e, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    exact (J.abs_pair_M u _).trans (mul_le_mul_of_nonneg_left (J.hQm x) (norm_nonneg _))
  have k3 := J.hHB x yp
  have hNx : ‖J.Nw x‖ ≤ J.CQ * ‖J.Mw.wi u‖ / Real.sqrt J.cw := by
    refine (J.Nw_le x).trans ?_
    exact div_le_div_of_nonneg_right hEx (Real.sqrt_nonneg _)
  have hNy : ‖J.Nw yp‖ ≤ J.Cy * ‖J.Mw.wi u‖ / Real.sqrt J.cw := by
    refine (J.Nw_le yp).trans ?_
    exact div_le_div_of_nonneg_right hEy (Real.sqrt_nonneg _)
  have hMu := norm_nonneg (J.Mw.wi u)
  have hdB := J.hdB
  have hκ := J.hκ0
  have k1' : |⟪ap - a0, yp⟫| ≤ J.dB * (J.Cy / Real.sqrt J.cw) * ‖J.Mw.wi u‖ ^ 2 := by
    refine k1.trans ?_
    have := mul_le_mul_of_nonneg_left hNy hdB
    have e : ‖J.Mw.wi u‖ * (J.dB * (J.Cy * ‖J.Mw.wi u‖ / Real.sqrt J.cw))
        = J.dB * (J.Cy / Real.sqrt J.cw) * ‖J.Mw.wi u‖ ^ 2 := by ring
    rw [← e]; exact mul_le_mul_of_nonneg_left this hMu
  have k2' : |⟪x, bp - a0⟫| ≤ J.dB * (J.CQ / Real.sqrt J.cw) * ‖J.Mw.wi u‖ ^ 2 := by
    refine k2.trans ?_
    have := mul_le_mul_of_nonneg_left hNx hdB
    have e : ‖J.Mw.wi u‖ * (J.dB * (J.CQ * ‖J.Mw.wi u‖ / Real.sqrt J.cw))
        = J.dB * (J.CQ / Real.sqrt J.cw) * ‖J.Mw.wi u‖ ^ 2 := by ring
    rw [← e]; exact mul_le_mul_of_nonneg_left this hMu
  have k3' : |⟪x, cjp J.ωE J.ωE J.Ginv yp⟫ - ⟪x, J.Ginv yp⟫| ≤ J.κ * (J.CQ * J.Cy) * ‖J.Mw.wi u‖ ^ 2 := by
    refine k3.trans ?_
    have h1 : Real.sqrt ⟪x, J.Ginv x⟫ * Real.sqrt ⟪yp, J.Ginv yp⟫ ≤ (J.CQ * ‖J.Mw.wi u‖) * (J.Cy * ‖J.Mw.wi u‖) :=
      mul_le_mul hEx hEy (Real.sqrt_nonneg _) (mul_nonneg J.hCQ hMu)
    have e : J.κ * ((J.CQ * ‖J.Mw.wi u‖) * (J.Cy * ‖J.Mw.wi u‖)) = J.κ * (J.CQ * J.Cy) * ‖J.Mw.wi u‖ ^ 2 := by ring
    rw [← e]; exact mul_le_mul_of_nonneg_left h1 hκ
  rw [hNp, hrep, hN]
  have := (abs_le.mp k1').1
  have := (abs_le.mp k2').1
  have := (abs_le.mp k3').2
  unfold EN
  nlinarith

theorem N_cjp_coer (u : F) : (1 / J.bN - J.EN) * ‖J.Mw.wi u‖ ^ 2 ≤ ⟪u, cjp J.ωF J.ωF J.N u⟫ := by
  have h1 := J.N_lower u
  have h2 := J.cjpN_lower u
  have hb := J.hbN
  have h3 : ‖J.Mw.wi u‖ ^ 2 / J.bN ≤ ⟪u, J.N u⟫ := by rw [div_le_iff₀ hb]; linarith
  have e : (1 / J.bN - J.EN) * ‖J.Mw.wi u‖ ^ 2 = ‖J.Mw.wi u‖ ^ 2 / J.bN - J.EN * ‖J.Mw.wi u‖ ^ 2 := by ring
  rw [e]; linarith

theorem cjpN_Ninv (w : F) : cjp J.ωF J.ωF J.N (cjp J.ωF J.ωF J.Ninv w) = w := by
  rw [cjp_apply, cjp_apply, J.ωF.wi_w]
  have := J.hN1 (J.ωF.wi w)
  rw [show J.N (J.Ninv (J.ωF.wi w)) = J.ωF.wi w from this, J.ωF.w_wi]

/-- **`cN ‖M (N⁻¹)⁺ w‖ ≤ ‖M⁻¹ w‖`** -/
theorem Ninv_cjp (hcN : 0 < 1 / J.bN - J.EN) (w : F) :
    (1 / J.bN - J.EN) * ‖J.Mw.wi (cjp J.ωF J.ωF J.Ninv w)‖ ≤ ‖J.Mw.w w‖ := by
  set u := cjp J.ωF J.ωF J.Ninv w with hu
  have h1 := J.N_cjp_coer u
  rw [J.cjpN_Ninv w] at h1
  have h2 : ⟪u, w⟫ ≤ ‖J.Mw.wi u‖ * ‖J.Mw.w w‖ := by
    have := J.abs_pair_M u w
    exact (le_abs_self _).trans this
  have hMu := norm_nonneg (J.Mw.wi u)
  by_cases h0 : ‖J.Mw.wi u‖ = 0
  · rw [h0, mul_zero]; exact norm_nonneg _
  have hpos : 0 < ‖J.Mw.wi u‖ := lt_of_le_of_ne hMu (Ne.symm h0)
  have : (1 / J.bN - J.EN) * ‖J.Mw.wi u‖ * ‖J.Mw.wi u‖ ≤ ‖J.Mw.w w‖ * ‖J.Mw.wi u‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

theorem cjpH_eq : cjp J.ωF J.ωE J.H
    = cjp J.ωE J.ωE J.Gi ∘L ContinuousLinearMap.adjoint (cjm J.ωE J.ωF J.Q) ∘L cjp J.ωF J.ωF J.Ninv := by
  unfold H
  rw [cjp_comp J.ωF J.ωE J.ωE, cjp_comp J.ωF J.ωF J.ωE, adjoint_cjm]

/-- the constant of the weighted `H` bound -/
noncomputable def CHw : ℝ := J.Cy / Real.sqrt J.cw * (1 / (1 / J.bN - J.EN))

/-- **the weighted `H⁺` bound**: `‖Nw H⁺ w‖ ≤ CHw ‖M⁻¹ w‖` -/
theorem H_cjp_w (hcN : 0 < 1 / J.bN - J.EN) (w : F) :
    ‖J.Nw (cjp J.ωF J.ωE J.H w)‖ ≤ J.CHw * ‖J.Mw.w w‖ := by
  set y := cjp J.ωF J.ωF J.Ninv w with hy
  set b := ContinuousLinearMap.adjoint (cjm J.ωE J.ωF J.Q) y with hb
  set h := cjp J.ωE J.ωE J.Gi b with hh
  have eH : cjp J.ωF J.ωE J.H w = h := by rw [cjpH_eq]; rfl
  rw [eH]
  have hG : cjp J.ωE J.ωE J.Ginv h = b := J.cjpGinv_Gi b
  have hE := J.sqrtE_of_pair h y (by rw [hG, hb, ContinuousLinearMap.adjoint_inner_right, real_inner_comm])
  have hN := J.Ninv_cjp hcN w
  rw [← hy] at hN
  have hMy : ‖J.Mw.wi y‖ ≤ ‖J.Mw.w w‖ / (1 / J.bN - J.EN) := by
    rw [le_div_iff₀ hcN]; linarith
  refine (J.Nw_le h).trans ?_
  have hc := Real.sqrt_pos.mpr J.hcw
  have hCy := J.Cy_nonneg
  calc Real.sqrt (J.En h) / Real.sqrt J.cw ≤ (J.Cy * ‖J.Mw.wi y‖) / Real.sqrt J.cw :=
        div_le_div_of_nonneg_right hE hc.le
    _ ≤ (J.Cy * (‖J.Mw.w w‖ / (1 / J.bN - J.EN))) / Real.sqrt J.cw :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMy hCy) hc.le
    _ = J.CHw * ‖J.Mw.w w‖ := by unfold CHw; field_simp

end WSchur

#print axioms WSchur.N
#print axioms WSchur.H
#print axioms WSchur.En_nonneg
#print axioms WSchur.Nw_le
#print axioms WSchur.pair_M
#print axioms WSchur.abs_pair_M
#print axioms WSchur.cjpGinv_Gi
#print axioms WSchur.cjp_form_lower
#print axioms WSchur.sqrtE_of_pair
#print axioms WSchur.N_lower
#print axioms WSchur.cjpN_eq
#print axioms WSchur.cjpN_lower
#print axioms WSchur.N_cjp_coer
#print axioms WSchur.cjpN_Ninv
#print axioms WSchur.Ninv_cjp
#print axioms WSchur.cjpH_eq
#print axioms WSchur.H_cjp_w

end AdalyFormal.M1DStrat
