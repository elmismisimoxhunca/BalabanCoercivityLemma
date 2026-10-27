import DLR9

/-!
# DL10 -- abstract weighted SITE chain: `G' = (D*D + m Q'*Q')⁻¹`, `DG'`, `G'D*`, `X = G'Q'*`, `Γ = X*X`

`SiteHyp` bundles: `D : S → E`, `Qp : S → Y`, `m ≥ 0`, `L = D*D + m Qp*Qp` with a two-sided inverse `Linv` and coercivity
`c‖f‖² ≤ ⟪f,Lf⟫`, weights `ωS, ωE, ωY`, commutator bounds `‖D^± − D‖ ≤ δD`, `‖Qp^± − Qp‖ ≤ δQ`, smallness `24(δD² + mδQ²) ≤ c`,
`4δD² ≤ c`.  Outputs (all for BOTH conjugations):
* `form_lower` : `⟪f, L⁺f⟫ ≥ ½⟪f,Lf⟫ − 3(δD² + mδQ²)‖f‖²`;  `cjp_coer` : `⟪f,L⁺f⟫ ≥ (c/4)‖f‖²`;
* `Linv_cjp` : `(c/4)‖(G')⁺g‖ ≤ ‖g‖`;  `D_Linv_cjp` : `‖D (G')⁺ g‖² ≤ (12/c)‖g‖²`;
* `LinvDadj_cjp` : for `h = (G')⁺ (D⁻)* v`: `‖h‖² ≤ (48/c)‖v‖²`, `‖Dh‖² ≤ 24‖v‖²`;
* `gamma_lower` : `‖u‖ ≤ q·b·‖X u‖` from a right inverse `Qp g = u` with `⟪g,Lg⟫ ≤ b‖u‖²` and `‖Qp‖ ≤ q` (no derivative bound needed).
With `c = c_s/n²`, `δD ~ θ/n`, `δQ ~ θ n^{−3/2}`, `m ~ a n` every output has its sharp power of `n` (DESIGN in REPORT).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

/-- the site-chain hypotheses -/
structure SiteHyp (S E Y : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] where
  D : S →L[ℝ] E
  Qp : S →L[ℝ] Y
  m : ℝ
  Linv : S →L[ℝ] S
  ωS : WPair S
  ωE : WPair E
  ωY : WPair Y
  c : ℝ
  δD : ℝ
  δQ : ℝ
  hm : 0 ≤ m
  hc : 0 < c
  hδD : 0 ≤ δD
  hδQ : 0 ≤ δQ
  hL1 : ∀ x, (ContinuousLinearMap.adjoint D ∘L D + m • (ContinuousLinearMap.adjoint Qp ∘L Qp)) (Linv x) = x
  hL2 : ∀ x, Linv ((ContinuousLinearMap.adjoint D ∘L D + m • (ContinuousLinearMap.adjoint Qp ∘L Qp)) x) = x
  hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ ⟪f, (ContinuousLinearMap.adjoint D ∘L D + m • (ContinuousLinearMap.adjoint Qp ∘L Qp)) f⟫
  hDp : ‖cjp ωS ωE D - D‖ ≤ δD
  hDm : ‖cjm ωS ωE D - D‖ ≤ δD
  hQp : ‖cjp ωS ωY Qp - Qp‖ ≤ δQ
  hQm : ‖cjm ωS ωY Qp - Qp‖ ≤ δQ
  hsmall : 24 * (δD ^ 2 + m * δQ ^ 2) ≤ c
  hsmallD : 4 * δD ^ 2 ≤ c

namespace SiteHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (H : SiteHyp S E Y)

/-- `L = D*D + m Qp*Qp` -/
noncomputable def L : S →L[ℝ] S :=
  ContinuousLinearMap.adjoint H.D ∘L H.D + H.m • (ContinuousLinearMap.adjoint H.Qp ∘L H.Qp)

/-- the same hypotheses with the inverse weights (exchanges `⁺` and `⁻`) -/
def inv : SiteHyp S E Y :=
  { H with ωS := H.ωS.inv, ωE := H.ωE.inv, ωY := H.ωY.inv, hDp := H.hDm, hDm := H.hDp, hQp := H.hQm, hQm := H.hQp }

theorem inv_L : H.inv.L = H.L := rfl

theorem L_form (f : S) : ⟪f, H.L f⟫ = ‖H.D f‖ ^ 2 + H.m * ‖H.Qp f‖ ^ 2 := by
  simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem form_lower (f : S) :
    (1 / 2) * ⟪f, H.L f⟫ - 3 * (H.δD ^ 2 + H.m * H.δQ ^ 2) * ‖f‖ ^ 2 ≤ ⟪f, cjp H.ωS H.ωS H.L f⟫ := by
  have e : cjp H.ωS H.ωS H.L = cjp H.ωS H.ωS (ContinuousLinearMap.adjoint H.D ∘L H.D)
      + H.m • cjp H.ωS H.ωS (ContinuousLinearMap.adjoint H.Qp ∘L H.Qp) := by
    rw [L, cjp_add, cjp_smul]
  rw [e, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right, real_inner_smul_right]
  have h1 := xtx_cjp_lower H.ωS H.ωE H.D H.δD H.hδD H.hDp H.hDm f
  have h2 := xtx_cjp_lower H.ωS H.ωY H.Qp H.δQ H.hδQ H.hQp H.hQm f
  have h2' := mul_le_mul_of_nonneg_left h2 H.hm
  rw [L_form]
  nlinarith [H.hm]

theorem cjp_coer (f : S) : (H.c / 4) * ‖f‖ ^ 2 ≤ ⟪f, cjp H.ωS H.ωS H.L f⟫ := by
  have h1 := H.form_lower f
  have h2 : H.c * ‖f‖ ^ 2 ≤ ⟪f, H.L f⟫ := H.hcoer f
  have h3 := H.hsmall
  have hf := sq_nonneg ‖f‖
  have k1 := mul_nonneg (sub_nonneg.mpr h3) hf
  have k2 := mul_nonneg H.hc.le hf
  have e1 : (H.c - 24 * (H.δD ^ 2 + H.m * H.δQ ^ 2)) * ‖f‖ ^ 2
      = H.c * ‖f‖ ^ 2 - 8 * (3 * (H.δD ^ 2 + H.m * H.δQ ^ 2) * ‖f‖ ^ 2) := by ring
  rw [e1] at k1
  linarith

theorem cjp_L_Linv (g : S) : cjp H.ωS H.ωS H.L (cjp H.ωS H.ωS H.Linv g) = g := by
  rw [cjp_apply, cjp_apply, H.ωS.wi_w]
  have := H.hL1 (H.ωS.wi g)
  rw [show H.L (H.Linv (H.ωS.wi g)) = H.ωS.wi g from this, H.ωS.w_wi]

/-- `(c/4)‖(G')⁺ g‖ ≤ ‖g‖` -/
theorem Linv_cjp (g : S) : (H.c / 4) * ‖cjp H.ωS H.ωS H.Linv g‖ ≤ ‖g‖ :=
  inv_cjp_bound H.ωS H.L H.Linv (fun x => H.hL1 x) (H.c / 4) (fun h => H.cjp_coer h) g

/-- `‖D (G')⁺ g‖² ≤ (12/c)‖g‖²` -/
theorem D_Linv_cjp (g : S) : ‖H.D (cjp H.ωS H.ωS H.Linv g)‖ ^ 2 ≤ (12 / H.c) * ‖g‖ ^ 2 := by
  set h := cjp H.ωS H.ωS H.Linv g with hh
  have hL := H.cjp_L_Linv g
  rw [← hh] at hL
  have h1 := H.form_lower h
  rw [hL] at h1
  have h2 : ⟪h, g⟫ ≤ ‖h‖ * ‖g‖ := real_inner_le_norm h g
  have h3 := H.Linv_cjp g
  rw [← hh] at h3
  have hc := H.hc
  have hLf := H.L_form h
  have hm2 : 0 ≤ H.m * ‖H.Qp h‖ ^ 2 := mul_nonneg H.hm (sq_nonneg _)
  have hE : 3 * (H.δD ^ 2 + H.m * H.δQ ^ 2) ≤ H.c / 8 := by linarith [H.hsmall]
  have hhn : ‖h‖ ≤ (4 / H.c) * ‖g‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  have hE0 : 0 ≤ 3 * (H.δD ^ 2 + H.m * H.δQ ^ 2) := by
    have := H.hm; have := sq_nonneg H.δD; have := sq_nonneg H.δQ; positivity
  -- ‖Dh‖² ≤ ⟪h,Lh⟫ ≤ 2‖h‖‖g‖ + 2E‖h‖²
  have hD : ‖H.D h‖ ^ 2 ≤ 2 * (‖h‖ * ‖g‖) + 2 * (3 * (H.δD ^ 2 + H.m * H.δQ ^ 2)) * ‖h‖ ^ 2 := by
    nlinarith
  have hg0 := norm_nonneg g
  have hh0 := norm_nonneg h
  have k1 : ‖h‖ * ‖g‖ ≤ (4 / H.c) * ‖g‖ ^ 2 := by
    calc ‖h‖ * ‖g‖ ≤ ((4 / H.c) * ‖g‖) * ‖g‖ := mul_le_mul_of_nonneg_right hhn hg0
      _ = (4 / H.c) * ‖g‖ ^ 2 := by ring
  have k2 : ‖h‖ ^ 2 ≤ ((4 / H.c) * ‖g‖) ^ 2 := pow_le_pow_left₀ hh0 hhn 2
  have k3 : 2 * (3 * (H.δD ^ 2 + H.m * H.δQ ^ 2)) * ‖h‖ ^ 2 ≤ 2 * (H.c / 8) * ((4 / H.c) * ‖g‖) ^ 2 := by
    apply mul_le_mul (by linarith) k2 (sq_nonneg _) (by positivity)
  have k4 : 2 * (H.c / 8) * ((4 / H.c) * ‖g‖) ^ 2 = (4 / H.c) * ‖g‖ ^ 2 := by
    field_simp; ring
  have : 2 * (4 / H.c) * ‖g‖ ^ 2 + (4 / H.c) * ‖g‖ ^ 2 = (12 / H.c) * ‖g‖ ^ 2 := by ring
  linarith

/-- `(G')⁺ (D⁻)*`: `‖h‖² ≤ (48/c)‖v‖²`, `‖Dh‖² ≤ 24‖v‖²` -/
theorem LinvDadj_cjp (v : E) :
    ‖cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v)‖ ^ 2 ≤ (48 / H.c) * ‖v‖ ^ 2 ∧
    ‖H.D (cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v))‖ ^ 2 ≤ 24 * ‖v‖ ^ 2 := by
  set h := cjp H.ωS H.ωS H.Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v) with hh
  have hL := H.cjp_L_Linv (ContinuousLinearMap.adjoint (cjm H.ωS H.ωE H.D) v)
  rw [← hh] at hL
  have h1 := H.form_lower h
  rw [hL, ContinuousLinearMap.adjoint_inner_right] at h1
  -- ⟪D⁻h, v⟫ ≤ (‖Dh‖ + δD‖h‖)‖v‖
  have hDm : ‖cjm H.ωS H.ωE H.D h‖ ≤ ‖H.D h‖ + H.δD * ‖h‖ := by
    have e : cjm H.ωS H.ωE H.D h = H.D h + (cjm H.ωS H.ωE H.D - H.D) h := by
      rw [ContinuousLinearMap.sub_apply]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := (cjm H.ωS H.ωE H.D - H.D).le_opNorm h
    linarith [mul_le_mul_of_nonneg_right H.hDm (norm_nonneg h)]
  have hin : ⟪cjm H.ωS H.ωE H.D h, v⟫ ≤ (‖H.D h‖ + H.δD * ‖h‖) * ‖v‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hDm (norm_nonneg _))
  have hLf := H.L_form h
  have hco : H.c * ‖h‖ ^ 2 ≤ ⟪h, H.L h⟫ := H.hcoer h
  have hm2 : 0 ≤ H.m * ‖H.Qp h‖ ^ 2 := mul_nonneg H.hm (sq_nonneg _)
  have hE : 3 * (H.δD ^ 2 + H.m * H.δQ ^ 2) ≤ H.c / 8 := by linarith [H.hsmall]
  have hc := H.hc
  -- ⟪h, L⁺h⟫ ≥ ¼‖Dh‖² + (c/8)‖h‖²
  have hEh := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖h‖)
  have hlow : (1 / 4) * ‖H.D h‖ ^ 2 + (H.c / 8) * ‖h‖ ^ 2 ≤ (‖H.D h‖ + H.δD * ‖h‖) * ‖v‖ := by
    nlinarith
  have hδ := H.hsmallD
  have hv0 := norm_nonneg v
  have hh0 := norm_nonneg h
  have hDh0 := norm_nonneg (H.D h)
  -- AM-GM: ‖Dh‖‖v‖ ≤ ⅛‖Dh‖² + 2‖v‖²,  δD‖h‖‖v‖ ≤ (c/16)‖h‖² + (4δD²/c)‖v‖²
  have a1 : ‖H.D h‖ * ‖v‖ ≤ (1 / 8) * ‖H.D h‖ ^ 2 + 2 * ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖H.D h‖ - 4 * ‖v‖)]
  have a2 : H.δD * ‖h‖ * ‖v‖ ≤ (H.c / 16) * ‖h‖ ^ 2 + (4 * H.δD ^ 2 / H.c) * ‖v‖ ^ 2 := by
    have : 0 ≤ (H.c / 16) * (‖h‖ - (8 * H.δD / H.c) * ‖v‖) ^ 2 := by positivity
    have e : (H.c / 16) * (‖h‖ - (8 * H.δD / H.c) * ‖v‖) ^ 2
        = (H.c / 16) * ‖h‖ ^ 2 - H.δD * ‖h‖ * ‖v‖ + (4 * H.δD ^ 2 / H.c) * ‖v‖ ^ 2 := by
      field_simp; ring
    linarith
  have a3 : (4 * H.δD ^ 2 / H.c) * ‖v‖ ^ 2 ≤ 1 * ‖v‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [div_le_one hc]; linarith
  have key : (1 / 8) * ‖H.D h‖ ^ 2 + (H.c / 16) * ‖h‖ ^ 2 ≤ 3 * ‖v‖ ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]; nlinarith
  · nlinarith

/-- **Γ lower bound** (unweighted): `‖u‖ ≤ q b ‖G' Qp* u‖` from a right inverse with `⟪g,Lg⟫ ≤ b‖u‖²`. -/
theorem gamma_lower (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hQ : ‖H.Qp‖ ≤ q)
    (ext : ∀ u : Y, ∃ g : S, H.Qp g = u ∧ ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2) (u : Y) :
    ‖u‖ ≤ q * b * ‖H.Linv (ContinuousLinearMap.adjoint H.Qp u)‖ := by
  obtain ⟨g, hg, hgL⟩ := ext u
  set x := H.Linv (ContinuousLinearMap.adjoint H.Qp u) with hx
  have hLx : H.L x = ContinuousLinearMap.adjoint H.Qp u := H.hL1 _
  -- ‖u‖² = ⟪u, Qp g⟫ = ⟪L x, g⟫ = ⟪x, L g⟫
  have hsym : ∀ y z, ⟪H.L y, z⟫ = ⟪y, H.L z⟫ := by
    intro y z
    simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  have e1 : ‖u‖ ^ 2 = ⟪x, H.L g⟫ := by
    rw [← hsym, hLx, ContinuousLinearMap.adjoint_inner_left, hg, real_inner_self_eq_norm_sq]
  -- Cauchy–Schwarz for the positive form L
  have hpos : ∀ y, 0 ≤ ⟪y, H.L y⟫ := fun y => by rw [L_form]; have := H.hm; positivity
  have hCS : ⟪x, H.L g⟫ ^ 2 ≤ ⟪x, H.L x⟫ * ⟪g, H.L g⟫ := by
    -- discriminant of t ↦ ⟪x + t g, L(x + t g)⟫ ≥ 0
    have hq' : ∀ t : ℝ, 0 ≤ ⟪x, H.L x⟫ + 2 * t * ⟪x, H.L g⟫ + t ^ 2 * ⟪g, H.L g⟫ := by
      intro t
      have := hpos (x + t • g)
      have e : ⟪x + t • g, H.L (x + t • g)⟫ = ⟪x, H.L x⟫ + 2 * t * ⟪x, H.L g⟫ + t ^ 2 * ⟪g, H.L g⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        have : ⟪g, H.L x⟫ = ⟪x, H.L g⟫ := by rw [← hsym, real_inner_comm]
        rw [this]; ring
      rw [e] at this; exact this
    by_cases hg0 : ⟪g, H.L g⟫ = 0
    · have hx0 : ⟪x, H.L g⟫ = 0 := by
        by_contra hne
        have ht := hq' (-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫))
        have e : 2 * (-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫)) * ⟪x, H.L g⟫ = -(⟪x, H.L x⟫ + 1) := by
          field_simp
        rw [hg0, e] at ht
        linarith [ht, mul_zero ((-(⟪x, H.L x⟫ + 1) / (2 * ⟪x, H.L g⟫)) ^ 2)]
      rw [hx0, hg0]; simp
    · have hgpos : 0 < ⟪g, H.L g⟫ := lt_of_le_of_ne (hpos g) (Ne.symm hg0)
      have := hq' (-⟪x, H.L g⟫ / ⟪g, H.L g⟫)
      have e : ⟪x, H.L x⟫ + 2 * (-⟪x, H.L g⟫ / ⟪g, H.L g⟫) * ⟪x, H.L g⟫
          + (-⟪x, H.L g⟫ / ⟪g, H.L g⟫) ^ 2 * ⟪g, H.L g⟫
          = ⟪x, H.L x⟫ - ⟪x, H.L g⟫ ^ 2 / ⟪g, H.L g⟫ := by field_simp; ring
      rw [e] at this
      have h2 : ⟪x, H.L g⟫ ^ 2 / ⟪g, H.L g⟫ ≤ ⟪x, H.L x⟫ := by linarith
      rwa [div_le_iff₀ hgpos] at h2
  -- ⟪x, L x⟫ = ⟪Qp x, u⟫ ≤ q‖x‖‖u‖
  have hxLx : ⟪x, H.L x⟫ ≤ q * ‖x‖ * ‖u‖ := by
    rw [hLx, ContinuousLinearMap.adjoint_inner_right]
    refine (real_inner_le_norm _ _).trans ?_
    have := H.Qp.le_opNorm x
    have h2 : ‖H.Qp x‖ ≤ q * ‖x‖ := this.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  -- assemble: ‖u‖⁴ ≤ q‖x‖‖u‖ · b‖u‖²
  have hu4 : ‖u‖ ^ 4 ≤ (q * ‖x‖ * ‖u‖) * (b * ‖u‖ ^ 2) := by
    have h0 : 0 ≤ ⟪x, H.L x⟫ := hpos x
    have : ‖u‖ ^ 4 = ⟪x, H.L g⟫ ^ 2 := by rw [← e1]; ring
    rw [this]
    calc ⟪x, H.L g⟫ ^ 2 ≤ ⟪x, H.L x⟫ * ⟪g, H.L g⟫ := hCS
      _ ≤ (q * ‖x‖ * ‖u‖) * (b * ‖u‖ ^ 2) :=
          mul_le_mul hxLx hgL (hpos g) (by positivity)
  by_cases hu0 : ‖u‖ = 0
  · rw [hu0]; positivity
  have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
  have : ‖u‖ * ‖u‖ ^ 3 ≤ (q * b * ‖x‖) * ‖u‖ ^ 3 := by nlinarith
  have hu3 : 0 < ‖u‖ ^ 3 := by positivity
  exact le_of_mul_le_mul_right this hu3

end SiteHyp

#print axioms SiteHyp.L
#print axioms SiteHyp.inv
#print axioms SiteHyp.L_form
#print axioms SiteHyp.form_lower
#print axioms SiteHyp.cjp_coer
#print axioms SiteHyp.cjp_L_Linv
#print axioms SiteHyp.Linv_cjp
#print axioms SiteHyp.D_Linv_cjp
#print axioms SiteHyp.LinvDadj_cjp
#print axioms SiteHyp.gamma_lower

end AdalyFormal.DLayer
