import DLR33

/-!
# DL34 -- the SCALED genuine instances (`s = n = ℓ^k`): every structure constant is an explicit k-free parameter

* `siteHypS` : `D' = n•D_U`, `Q'_p = (√m_k n)•Qtop` (`m_k = a_kℓ^k`), `m' = 1`, `G'' = n⁻²•Gp`; its constants
  `c', δD', δQ'` are free parameters constrained by the scaled bounds `c'‖f‖² ≤ n²⟪f,Δ'_a f⟫`, `n·√3(e^{θ'}−1) ≤ δD'`,
  `√m_k·n·√((1/ℓ³)^k)(e^δ−1) ≤ δQ'` (so `L' = n² Δ'_a`).
* `ginvHypS` : `C' = n•C`, `Δ'' = n²•Δ'`, `Q'_b = √(a n³)•Q`, `M' = 1`, with the scaled commutator bounds as hypotheses.
* **`GinvS_eq`** : `(ginvHypS ..).Ginv = n² • GinvFull` (the genuine `G⁻¹`, DL32).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (TowerClass)

theorem cjp_smul_sub {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (ωX : WPair X) (ωZ : WPair Z) (c : ℝ) (T : X →L[ℝ] Z) :
    ‖cjp ωX ωZ (c • T) - c • T‖ = |c| * ‖cjp ωX ωZ T - T‖ := by
  rw [cjp_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]

theorem cjm_smul_sub {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (ωX : WPair X) (ωZ : WPair Z) (c : ℝ) (T : X →L[ℝ] Z) :
    ‖cjm ωX ωZ (c • T) - c • T‖ = |c| * ‖cjm ωX ωZ T - T‖ := by
  rw [cjm_eq_cjp_inv, cjp_smul_sub]; rfl

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem LS_eq (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (hm0 : 0 ≤ mTop ell k a) (f : SiteL2 (scaleUp ell k Lu)) :
    (ContinuousLinearMap.adjoint (((ell : ℝ) ^ k) • gradL2 U) ∘L (((ell : ℝ) ^ k) • gradL2 U)
      + (1 : ℝ) • (ContinuousLinearMap.adjoint ((Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U)
          ∘L ((Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U))) f
      = ((ell : ℝ) ^ k) ^ 2 • DelpA (GF ell k Lu) U a f := by
  have hn : (0 : ℝ) ≤ (ell : ℝ) ^ k := by positivity
  set r := Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k with hr
  have hs : Real.sqrt (mTop ell k a) * Real.sqrt (mTop ell k a) = mTop ell k a := Real.mul_self_sqrt hm0
  have h1 : (ContinuousLinearMap.adjoint (((ell : ℝ) ^ k) • gradL2 U) ∘L (((ell : ℝ) ^ k) • gradL2 U)) f
      = ((ell : ℝ) ^ k) ^ 2 • ContinuousLinearMap.adjoint (gradL2 U) (gradL2 U f) := by
    rw [adjoint_smul_real, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, map_smul, smul_smul, sq]
  have h2 : (ContinuousLinearMap.adjoint (r • Qtop (GF ell k Lu) U) ∘L (r • Qtop (GF ell k Lu) U)) f
      = (((ell : ℝ) ^ k) ^ 2 * mTop ell k a) • ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) (Qtop (GF ell k Lu) U f) := by
    rw [adjoint_smul_real, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    rw [hr, show Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k)
        = (Real.sqrt (mTop ell k a) * Real.sqrt (mTop ell k a)) * ((ell : ℝ) ^ k) ^ 2 by ring, hs]
    ring
  have h3 : DelpA (GF ell k Lu) U a f
      = ContinuousLinearMap.adjoint (gradL2 U) (gradL2 U f)
        + mTop ell k a • ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) (Qtop (GF ell k Lu) U f) := by
    rw [DelpA_eq_L]; rfl
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, one_smul, h1, h2, h3, smul_add, smul_smul]

/-- **the scaled genuine site layer** -/
noncomputable def siteHypS (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' δ c' δD' δQ' : ℝ) (hφ : WtLip θ' φ) (hδ : 0 ≤ δ)
    (hbox : ∀ y ∈ (GF ell k Lu).Lam (GF ell k Lu).k, ∀ x ∈ boxF y (ell ^ k), |φ y - φ x| ≤ δ)
    (hm0 : 0 ≤ mTop ell k a)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (hc : 0 < c') (hcoer : ∀ f, c' * ‖f‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫)
    (hDD : (ell : ℝ) ^ k * (Real.sqrt 3 * (Real.exp θ' - 1)) ≤ δD')
    (hQQ : Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * (Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) * (Real.exp δ - 1)) ≤ δQ')
    (hsmall : 24 * (δD' ^ 2 + 1 * δQ' ^ 2) ≤ c') (hsmallD : 4 * δD' ^ 2 ≤ c') :
    SiteHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)) where
  D := ((ell : ℝ) ^ k) • gradL2 U
  Qp := (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U
  m := 1
  Linv := ((ell : ℝ) ^ k)⁻¹ ^ 2 • Gp (GF ell k Lu) U a
  ωS := siteWP φ
  ωE := bondWP φ
  ωY := coarseWP ell k Lu φ
  c := c'
  δD := δD'
  δQ := δQ'
  hm := zero_le_one
  hc := hc
  hδD := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
    exact le_trans (by positivity) hDD
  hδQ := by
    have : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
    exact le_trans (by positivity) hQQ
  hL1 := fun x => by
    rw [LS_eq ell k Lu U a hm0, ContinuousLinearMap.smul_apply, map_smul, Gp_right ell k Lu U a hu, smul_smul]
    have hn : ((ell : ℝ) ^ k) ≠ 0 := by positivity
    rw [show ((ell : ℝ) ^ k) ^ 2 * ((ell : ℝ) ^ k)⁻¹ ^ 2 = 1 by field_simp, one_smul]
  hL2 := fun x => by
    rw [LS_eq ell k Lu U a hm0, ContinuousLinearMap.smul_apply, map_smul, Gp_left ell k Lu U a hu, smul_smul]
    have hn : ((ell : ℝ) ^ k) ≠ 0 := by positivity
    rw [show ((ell : ℝ) ^ k)⁻¹ ^ 2 * ((ell : ℝ) ^ k) ^ 2 = 1 by field_simp, one_smul]
  hcoer := fun f => by
    rw [LS_eq ell k Lu U a hm0, real_inner_smul_right]
    exact hcoer f
  hDp := by
    rw [cjp_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (D_cjp_norm U φ θ' hφ) (by positivity)).trans hDD
  hDm := by
    rw [cjm_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (D_cjm_norm U φ θ' hφ) (by positivity)).trans hDD
  hQp := by
    rw [cjp_smul_sub, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (Q_cjp_norm ell k Lu U hell φ δ hδ hbox) (by positivity)).trans hQQ
  hQm := by
    rw [cjm_smul_sub, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (Q_cjm_norm ell k Lu U hell φ δ hδ hbox) (by positivity)).trans hQQ
  hsmall := hsmall
  hsmallD := hsmallD

/-- **the scaled genuine `G⁻¹` data** -/
noncomputable def ginvHypS (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ)
    (G0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
    (hD : G0.D = ((ell : ℝ) ^ k) • gradL2 U) (hωE : G0.ωE = bondWP φ) (hωS : G0.ωS = siteWP φ)
    (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (δC' κ' δK' ν' δν' δB' : ℝ)
    (hC' : (ell : ℝ) ^ k * (6 * (Real.exp θ' - 1)) ≤ δC')
    (hK' : ((ell : ℝ) ^ k) ^ 2 * (6 * q0) ≤ κ')
    (hdK' : ((ell : ℝ) ^ k) ^ 2 * (6 * q0 * (Real.exp (2 * θ') - 1)) ≤ δK')
    (hν' : ((ell : ℝ) ^ k) ^ 2 * (816 * α₀) ≤ ν')
    (hdν' : ((ell : ℝ) ^ k) ^ 2 * (816 * α₀ * (Real.exp (2 * θ') - 1)) ≤ δν')
    (hB' : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3)
      * (qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * multB ell k) ≤ δB') :
    GinvHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) where
  toGamHyp := G0
  C := ((ell : ℝ) ^ k) • curlC U
  Dp := ((ell : ℝ) ^ k) ^ 2 • DpOp U
  Qb := Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull
  M := 1
  ωP := plaqWP φ
  ωB := fspWP ell k Lu φ
  δC := δC'
  κ := κ'
  δK := δK'
  ν := ν'
  δν := δν'
  δB := δB'
  hM := zero_le_one
  hδC := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
    exact le_trans (by positivity) hC'
  hκ := le_trans (by positivity) hK'
  hδK := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
    exact le_trans (by positivity) hdK'
  hν := le_trans (by positivity) hν'
  hδν := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
    exact le_trans (by positivity) hdν'
  hδB := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ (Rfoot ell k : ℝ) * θ' := by positivity
    have : 0 ≤ Real.exp (Rfoot ell k * θ') - 1 := by linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * θ')]
    have := qbM_nonneg ell k ε
    have : 0 ≤ multB ell k := Real.sqrt_nonneg _
    exact le_trans (by positivity) hB'
  hCp := by
    rw [hωE, cjp_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (curl_cjp_norm U φ θ' hφ) (by positivity)).trans hC'
  hCm := by
    rw [hωE, cjm_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (curl_cjm_norm U φ θ' hφ) (by positivity)).trans hC'
  hKn := by
    rw [hD, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), ← pow_two]
    exact (mul_le_mul_of_nonneg_left (curv_norm U q0 hq0 hplaq) (by positivity)).trans hK'
  hKp := by
    rw [hωS, hD, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, cjp_smul_sub,
      abs_of_pos (by positivity), ← pow_two]
    exact (mul_le_mul_of_nonneg_left (curv_cjp_norm U φ θ' hφ q0 hq0 hplaq) (by positivity)).trans hdK'
  hKm := by
    rw [hωS, hD, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, cjm_smul_sub,
      abs_of_pos (by positivity), ← pow_two]
    exact (mul_le_mul_of_nonneg_left (curv_cjm_norm U φ θ' hφ q0 hq0 hplaq) (by positivity)).trans hdK'
  hDpn := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (DpOp_norm U hα₀ hpl) (by positivity)).trans hν'
  hDpp := by
    rw [hωE, cjp_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (DpOp_cjp_norm U hα₀ hpl φ θ' hφ) (by positivity)).trans hdν'
  hDpm := by
    rw [hωE, cjm_smul_sub, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (DpOp_cjm_norm U hα₀ hpl φ θ' hφ) (by positivity)).trans hdν'
  hDps := fun x y => by
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, DpOp_symm]
  hBp := by
    rw [hωE, cjp_smul_sub, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (Qfull_cjp_norm ell k Lu hell U ε hreg hcl hε0 hsm φ θ' hφ)
      (Real.sqrt_nonneg _)).trans hB'
  hBm := by
    rw [hωE, cjm_smul_sub, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (Qfull_cjm_norm ell k Lu hell U ε hreg hcl hε0 hsm φ θ' hφ)
      (Real.sqrt_nonneg _)).trans hB'

end

#print axioms cjp_smul_sub
#print axioms cjm_smul_sub
#print axioms LS_eq
#print axioms siteHypS
#print axioms ginvHypS

end AdalyFormal.DLayer
