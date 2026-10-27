import DLR41

/-!
# DL42 -- **`G_CT_M0`: the concrete, k-uniform Combes–Thomas bound for the genuine `G` at M0**

`‖e^{φ} G e^{−φ} g‖ ≤ 2 n² K̂ ‖g‖`, `G = (GinvFull)⁻¹` (the genuine `G⁻¹ = Δ_π + T*T + Q*aQ` of (3.122) on all fine bonds of the
full tower), for every weight `φ` with one-fine-step Lipschitz constant `θ/n`, provided `CondM0 ℓ a ρ θ` and
`4·EGM0 ℓ a ρ θ ≤ 1/K̂` — conditions on `(ℓ, a, t, ρ, θ)` only (no `k`, no volume).
Also `m0_scaled_instances` (the instance and its identities) for reuse by the `N`/`H` layer.
-/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 200000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0)
  (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
  (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)

/-- the scaled genuine site instance at M0 -/
noncomputable def siteM0 : SiteHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)) :=
  siteHypS ell k Lu (by have := R.hell; omega) U a φ (θ / (ell : ℝ) ^ k) (3 * θ) (cS a (rhoM0 ell k e q0)) (δDS θ) (δQS a θ)
    hφ (by have := hc.hθ; positivity) (m0_hbox ell k Lu U a t e q0 R φ θ hc.hθ hφ)
    (m0_mTop_pos ell k Lu U a t e q0 R).le (m0_hu ell k Lu U a t e q0 R) hc.cS_pos
    (m0_hcoerS ell k Lu U a t e q0 R) (m0_hDD ell k Lu U a t e q0 R θ hc.hθ) (m0_hQQ ell k Lu U a t e q0 R θ hc.hθ)
    hc.hS1 hc.hS2

theorem siteM0_L (g : SiteL2 (scaleUp ell k Lu)) :
    (siteM0 ell k Lu U a t e q0 R φ θ hφ hc).L g = ((ell : ℝ) ^ k) ^ 2 • DelpA (GF ell k Lu) U a g :=
  LS_eq ell k Lu U a (m0_mTop_pos ell k Lu U a t e q0 R).le g

/-- the scaled genuine `Γ` instance at M0 -/
noncomputable def gamM0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)) :=
  gamHypOf (siteM0 ell k Lu U a t e q0 R φ θ hφ hc) (qS a) (bS ell a (rhoM0 ell k e q0)) (cGS ell a (rhoM0 ell k e q0) θ)
    hc.qS_nonneg hc.bS_pos.le (mul_pos (Real.sqrt_pos.mpr hc.ha) hc.bS_pos)
    (m0_hQbS ell k Lu U a t e q0 R)
    (fun u => by
      obtain ⟨g, hg, hgE⟩ := m0_extS ell k Lu U a t e q0 R θ hc u
      refine ⟨g, hg, ?_⟩
      rw [siteM0_L, real_inner_smul_right]
      exact hgE)
    hc.hcG (le_of_eq rfl)

/-- the scaled genuine `G⁻¹` instance at M0 -/
noncomputable def ginvM0 (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0)) :
    GinvHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) :=
  ginvHypS ell k Lu (by have := R.hell; omega) U a R.ha.le φ (θ / (ell : ℝ) ^ k) hφ
    (gamM0 ell k Lu U a t e q0 R φ θ hφ hc) rfl rfl rfl q0 R.hq0 R.hplaq (q0 / (4 * Real.sqrt 2))
    (by have := R.hq0; positivity) (m0_hpl ell k Lu U a t e q0 R) (epsCl ell e q0)
    (AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H)
    (m0_cl ell k Lu U a t e q0 R) (m0_hε0 ell k Lu U a t e q0 R) (m0_hsm ell k Lu U a t e q0 R)
    (δCS θ) (κS (rhoM0 ell k e q0)) (δKS (rhoM0 ell k e q0) θ) (νS (rhoM0 ell k e q0)) (δνS (rhoM0 ell k e q0) θ)
    (δBS ell a (rhoM0 ell k e q0) θ)
    (m0_hC' ell k Lu U a t e q0 R θ hc.hθ) (m0_hK' ell k Lu U a t e q0 R) (m0_hdK' ell k Lu U a t e q0 R θ hc.hθ)
    (m0_hν' ell k Lu U a t e q0 R) (m0_hdν' ell k Lu U a t e q0 R θ hc.hθ) (m0_hB' ell k Lu U a t e q0 R θ hc.hθ)

theorem ginvM0_eq (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0)) : (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv = ((ell : ℝ) ^ k) ^ 2 • GinvFull ell k Lu U a :=
  GinvS_eq ell k Lu (by have := R.hell; omega) U a R.ha.le (m0_hu ell k Lu U a t e q0 R) φ (θ / (ell : ℝ) ^ k) hφ
    (gamM0 ell k Lu U a t e q0 R φ θ hφ hc) (m0_mTop_pos ell k Lu U a t e q0 R).le rfl rfl rfl
    (m0_mTop_pos ell k Lu U a t e q0 R) rfl rfl q0 R.hq0 R.hplaq (q0 / (4 * Real.sqrt 2))
    (by have := R.hq0; positivity) (m0_hpl ell k Lu U a t e q0 R) (epsCl ell e q0)
    (AdalyFormal.RegBgKU.regTower_M0_kuniform ell k Lu R.hell U e q0 R.he0 R.hq0 R.hlinks R.hplaq H)
    (m0_cl ell k Lu U a t e q0 R) (m0_hε0 ell k Lu U a t e q0 R) (m0_hsm ell k Lu U a t e q0 R)
    (δCS θ) (κS (rhoM0 ell k e q0)) (δKS (rhoM0 ell k e q0) θ) (νS (rhoM0 ell k e q0)) (δνS (rhoM0 ell k e q0) θ)
    (δBS ell a (rhoM0 ell k e q0) θ)
    (m0_hC' ell k Lu U a t e q0 R θ hc.hθ) (m0_hK' ell k Lu U a t e q0 R) (m0_hdK' ell k Lu U a t e q0 R θ hc.hθ)
    (m0_hν' ell k Lu U a t e q0 R) (m0_hdν' ell k Lu U a t e q0 R θ hc.hθ) (m0_hB' ell k Lu U a t e q0 R θ hc.hθ)

/-- **the error constant of the genuine scaled instance is the k-free `EGM0`** -/
theorem ginvM0_EG (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0)) : (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).EG = EGM0 ell a (rhoM0 ell k e q0) θ hc := rfl

end

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0)
include R

theorem KhatM0_pos : 0 < KhatM0 ell a t (rhoM0 ell k e q0) := by
  unfold KhatM0
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have h1 : 0 < 1 - 216 * rhoM0 ell k e q0 ^ 2 := by linarith [R.h216]
  have h2 : 0 < Mc a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  positivity

end

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
include R H

/-- `G⁻¹ ≥ 1/(n²K̂)` in the form used by `coercive_isUnit` -/
theorem GinvFull_coer' (f : BondFnL2 (scaleUp ell k Lu)) :
    (1 / (((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0))) * ‖f‖ ^ 2 ≤ ⟪f, GinvFull ell k Lu U a f⟫ := by
  have h := GinvFull_coercive ell k Lu U a t e q0 R H f
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  have hpos : 0 < ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  linarith

/-- the genuine `G⁻¹` (all fine bonds, full tower) is invertible at M0 -/
theorem GinvFull_isUnit : IsUnit (GinvFull ell k Lu U a) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  exact coercive_isUnit _ (by positivity) (GinvFull_coer' ell k Lu U a t e q0 R H)

/-- **`G_CT_M0` — the concrete Combes–Thomas bound for the genuine `G` at M0, k- and volume-uniform.**
For every weight `φ` whose one-fine-step increments are `≤ θ/n` (`n = ℓ^k`), under the k-free conditions
`CondM0 ℓ a ρ θ` and `4·EGM0 ℓ a ρ θ ≤ 1/K̂`:
`‖e^{φ} G (e^{−φ} g)‖ ≤ 2 n² K̂ ‖g‖`, `G = (GinvFull)⁻¹` (`Ring.inverse`, a true inverse by `GinvFull_isUnit`). -/
theorem G_CT_M0 (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
    (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
    (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0))
    (g : BondFnL2 (scaleUp ell k Lu)) :
    ‖bondWt φ (Ring.inverse (GinvFull ell k Lu U a) (bondWt (-φ) g))‖
      ≤ 2 * ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0) * ‖g‖ := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hn2 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by positivity
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  have hu := GinvFull_isUnit ell k Lu U a t e q0 R H
  set I := ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H with hI
  set Gi : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
    (((ell : ℝ) ^ k) ^ 2)⁻¹ • Ring.inverse (GinvFull ell k Lu U a) with hGidef
  have hGi : ∀ x, I.Ginv (Gi x) = x := by
    intro x
    rw [hI, ginvM0_eq, hGidef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul,
      mul_inv_cancel₀ hn2.ne', one_smul, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu,
      ContinuousLinearMap.one_apply]
  have hcoer : ∀ f, (1 / KhatM0 ell a t (rhoM0 ell k e q0)) * ‖f‖ ^ 2 ≤ ⟪f, I.Ginv f⟫ := by
    intro f
    rw [hI, ginvM0_eq, ContinuousLinearMap.smul_apply, real_inner_smul_right]
    have h := GinvFull_coercive ell k Lu U a t e q0 R H f
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK]
    nlinarith [h]
  have hE : 4 * I.EG ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0) := by
    rw [hI, ginvM0_EG]; exact hEG
  have hmain := GinvHyp.G_cjp_le I Gi hGi (1 / KhatM0 ell a t (rhoM0 ell k e q0)) (by positivity) hcoer hE g
  have hcj : cjp I.ωE I.ωE Gi g
      = (((ell : ℝ) ^ k) ^ 2)⁻¹ • bondWt φ (Ring.inverse (GinvFull ell k Lu U a) (bondWt (-φ) g)) := by
    show bondWt φ (Gi (bondWt (-φ) g)) = _
    rw [hGidef, ContinuousLinearMap.smul_apply, map_smul]
  rw [hcj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn2)] at hmain
  set X := ‖bondWt φ (Ring.inverse (GinvFull ell k Lu U a) (bondWt (-φ) g))‖
  have hX : 0 ≤ X := norm_nonneg _
  have e1 : 1 / KhatM0 ell a t (rhoM0 ell k e q0) / 2 * ((((ell : ℝ) ^ k) ^ 2)⁻¹ * X)
      = X / (2 * ((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0)) := by
    field_simp
  rw [e1, div_le_iff₀ (by positivity)] at hmain
  linarith

end

#print axioms siteM0
#print axioms gamM0
#print axioms ginvM0
#print axioms ginvM0_eq
#print axioms ginvM0_EG
#print axioms KhatM0_pos
#print axioms GinvFull_coer'
#print axioms GinvFull_isUnit
#print axioms G_CT_M0

end AdalyFormal.DLayer
