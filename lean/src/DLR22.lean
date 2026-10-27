import DLR21

/-!
# DL22 -- `GamHyp` from a right inverse (generic), and the genuine site/Γ instances at M0

* `SiteHyp.Gam_isUnit` (generic) : a right inverse of `Qp` with `⟪g,Lg⟫ ≤ b‖u‖²` makes `Γ = X*X` coercive (`⟪u,Γu⟫ ≥ ‖u‖²/(qb)²`), hence a unit.
* `gamHypOf` (generic) : `GamHyp` with `Γ⁻¹ := Ring.inverse Γ` (both inverse laws proved).
* `siteHypM0` : the genuine `(D_U, Qtop, a_kℓ^k, G' = Gp, e^{±φ})` as a `SiteHyp` (hypotheses: site unit `hu`, coercivity of `Δ'_a`, smallness).
* `extM0` : the genuine right inverse of `Qtop U` with energy `⟪g,Lg⟫ ≤ (B'² + m)‖w‖²`, `B' = (bFE + δ·aFE)/(1 − ε0·aFE)`
  (FlatExt `flatE` + `hext_of_flatExt`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)

namespace SiteHyp

variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y]
variable (H : SiteHyp S E Y)

theorem Gam_coer_of (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hqb : 0 < q * b) (hQ : ‖H.Qp‖ ≤ q)
    (ext : ∀ u : Y, ∃ g : S, H.Qp g = u ∧ ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2) (u : Y) :
    (1 / (q * b) ^ 2) * ‖u‖ ^ 2 ≤ ⟪u, H.Gam u⟫ := by
  have h2 := H.gamma_lower q b hq hb hQ ext u
  rw [Gam, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have e : (1 / (q * b) ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 / (q * b) ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)]
  show ‖u‖ ^ 2 ≤ ‖H.Linv (ContinuousLinearMap.adjoint H.Qp u)‖ ^ 2 * (q * b) ^ 2
  nlinarith [h3]

theorem Gam_isUnit [FiniteDimensional ℝ Y] (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hqb : 0 < q * b) (hQ : ‖H.Qp‖ ≤ q)
    (ext : ∀ u : Y, ∃ g : S, H.Qp g = u ∧ ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2) : IsUnit H.Gam :=
  coercive_isUnit H.Gam (by positivity) (H.Gam_coer_of q b hq hb hqb hQ ext)

end SiteHyp

section gen
variable {S E Y : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [FiniteDimensional ℝ Y]

/-- `GamHyp` with `Γ⁻¹ := Ring.inverse Γ` -/
noncomputable def gamHypOf (H : SiteHyp S E Y) (q b cG : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hqb : 0 < q * b)
    (hQ : ‖H.Qp‖ ≤ q) (ext : ∀ u : Y, ∃ g : S, H.Qp g = u ∧ ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2)
    (hcG : 0 < cG) (hcGdef : cG ≤ 1 / (2 * (q * b) ^ 2) - 3 * H.epsX q ^ 2) : GamHyp S E Y where
  toSiteHyp := H
  q := q
  b := b
  Gami := Ring.inverse H.Gam
  cG := cG
  hq := hq
  hb := hb
  hQ := hQ
  ext := ext
  hG1 := fun u => by
    show H.Gam (Ring.inverse H.Gam u) = u
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ (H.Gam_isUnit q b hq hb hqb hQ ext),
      ContinuousLinearMap.one_apply]
  hG2 := fun u => by
    show Ring.inverse H.Gam (H.Gam u) = u
    rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ (H.Gam_isUnit q b hq hb hqb hQ ext),
      ContinuousLinearMap.one_apply]
  hcG := hcG
  hcGdef := hcGdef

theorem gamHypOf_Gami (H : SiteHyp S E Y) (q b cG : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hqb : 0 < q * b)
    (hQ : ‖H.Qp‖ ≤ q) (ext : ∀ u : Y, ∃ g : S, H.Qp g = u ∧ ⟪g, H.L g⟫ ≤ b * ‖u‖ ^ 2)
    (hcG : 0 < cG) (hcGdef : cG ≤ 1 / (2 * (q * b) ^ 2) - 3 * H.epsX q ^ 2) :
    (gamHypOf H q b cG hq hb hqb hQ ext hcG hcGdef).Gami = Ring.inverse H.Gam := rfl

end gen

/-! ## the genuine instances -/

section concrete
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

/-- the genuine `L = D*D + m Qtop*Qtop` equals `Δ'_a` -/
theorem L_eq_DelpA (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (f : SiteL2 (scaleUp ell k Lu)) :
    (ContinuousLinearMap.adjoint (gradL2 U) ∘L gradL2 U
        + mTop ell k a • (ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) ∘L Qtop (GF ell k Lu) U)) f
      = DelpA (GF ell k Lu) U a f :=
  (DelpA_eq_L ell k Lu U a f).symm

/-- **the genuine site layer as a `SiteHyp`** -/
noncomputable def siteHypM0 (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' δ c : ℝ) (hφ : WtLip θ' φ) (hδ : 0 ≤ δ)
    (hbox : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ δ)
    (hm0 : 0 ≤ mTop ell k a)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (hc : 0 < c) (hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ ⟪f, DelpA (GF ell k Lu) U a f⟫)
    (hsmall : 24 * ((Real.sqrt 3 * (Real.exp θ' - 1)) ^ 2
        + mTop ell k a * (Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1)) ^ 2) ≤ c)
    (hsmallD : 4 * (Real.sqrt 3 * (Real.exp θ' - 1)) ^ 2 ≤ c) :
    SiteHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)) where
  D := gradL2 U
  Qp := Qtop (GF ell k Lu) U
  m := mTop ell k a
  Linv := Gp (GF ell k Lu) U a
  ωS := siteWP φ
  ωE := bondWP φ
  ωY := coarseWP ell k Lu φ
  c := c
  δD := Real.sqrt 3 * (Real.exp θ' - 1)
  δQ := Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1)
  hm := hm0
  hc := hc
  hδD := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
    positivity
  hδQ := by
    have : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
    positivity
  hL1 := fun x => by rw [L_eq_DelpA]; exact Gp_right ell k Lu U a hu x
  hL2 := fun x => by rw [L_eq_DelpA]; exact Gp_left ell k Lu U a hu x
  hcoer := fun f => by rw [L_eq_DelpA]; exact hcoer f
  hDp := D_cjp_norm U φ θ' hφ
  hDm := D_cjm_norm U φ θ' hφ
  hQp := Q_cjp_norm ell k Lu U hell φ δ hδ hbox
  hQm := Q_cjm_norm ell k Lu U hell φ δ hδ hbox
  hsmall := hsmall
  hsmallD := hsmallD

/-- the genuine right inverse of `Qtop U` with an energy bound (FlatExt + perturbation) -/
theorem extM0 (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (hm0 : 0 ≤ mTop ell k a) (δ ε0 : ℝ)
    (hδ : 0 ≤ δ) (hε0 : 0 ≤ ε0) (hεa : ε0 * AdalyFormal.FlatExt.aFE ell k < 1)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (w : coarseC (GF ell k Lu)) :
    ∃ g, Qtop (GF ell k Lu) U g = w ∧
      ⟪g, (ContinuousLinearMap.adjoint (gradL2 U) ∘L gradL2 U
        + mTop ell k a • (ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) ∘L Qtop (GF ell k Lu) U)) g⟫
      ≤ (((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k)
            / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) ^ 2 + mTop ell k a) * ‖w‖ ^ 2 := by
  obtain ⟨g, hg, hgD⟩ := AdalyFormal.SliceCoerc.hext_of_flatExt ell k Lu U (AdalyFormal.FlatExt.flatE ell k Lu)
    (AdalyFormal.FlatExt.aFE ell k) (AdalyFormal.FlatExt.bFE ell k) δ ε0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hδ hε0 hεa (AdalyFormal.FlatExt.flatE_rightInv ell k Lu hell) (AdalyFormal.FlatExt.flatE_norm_le ell k Lu hell)
    (AdalyFormal.FlatExt.flatE_grad_norm_le ell k Lu hell) hd hdrift w
  refine ⟨g, hg, ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hg]
  set B' := (AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k)
    / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k) with hB'
  have hB0 : 0 ≤ B' := by
    rw [hB']
    have : 0 < 1 - ε0 * AdalyFormal.FlatExt.aFE ell k := by linarith
    have h1 := Real.sqrt_nonneg (78732 * (ell : ℝ) ^ k)
    have h2 := Real.sqrt_nonneg (729 * ((ell : ℝ) ^ k) ^ 3)
    unfold AdalyFormal.FlatExt.bFE AdalyFormal.FlatExt.aFE
    positivity
  have h2 : ‖gradL2 U g‖ ^ 2 ≤ (B' * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgD 2
  nlinarith [mul_pow B' ‖w‖ 2]

end concrete

#print axioms SiteHyp.Gam_coer_of
#print axioms SiteHyp.Gam_isUnit
#print axioms gamHypOf
#print axioms gamHypOf_Gami
#print axioms L_eq_DelpA
#print axioms siteHypM0
#print axioms extM0

end AdalyFormal.DLayer
