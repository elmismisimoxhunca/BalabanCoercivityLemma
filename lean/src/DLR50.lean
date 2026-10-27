import DLR49

/-!
# DL50 -- **`bondExtM0`**: the bond competitor of the scaled genuine `G⁻¹` at M0 has k-FREE energy `bNS`

For `I = ginvM0 ..` (the scaled genuine instance, DL42) and every `u : FSp`:
`∃ g, I.Qb g = u ∧ ⟪g, I.Ginv g⟫ ≤ bNS a ρ δ ‖u‖²` (`δ = δS ℓ ρ`, DL49).  `g = Eop (Sinv (u/√(a n³)))`.
This is the `extN` field of the M0 Schur-complement structure (DL51): it gives the SHARP lower bound `N' ≥ 1/bNS`.
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
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)

theorem sqrt_cube (n : ℝ) (hn : 0 ≤ n) : Real.sqrt (n ^ 3) = n * Real.sqrt n := by
  have h : n ^ 3 = (n * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn]; ring
  rw [h, Real.sqrt_sq (by positivity)]

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))

include R in
theorem m0_ne_le : (ell : ℝ) ^ k * e ≤ rhoM0 ell k e q0 := by
  unfold rhoM0
  have := R.he0; have := R.hq0; have := Real.pi_pos
  have hn : (0 : ℝ) ≤ (ell : ℝ) ^ k := by positivity
  nlinarith [mul_nonneg hn (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) Real.pi_pos.le) (mul_nonneg hn R.hq0))]

/-- **the competitor** -/
theorem bondExtM0 (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
    (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ) (u : FSp (GF ell k Lu)) :
    ∃ g : BondFnL2 (scaleUp ell k Lu), (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Qb g = u ∧
      ⟪g, (ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H).Ginv g⟫
        ≤ bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) * ‖u‖ ^ 2 := by
  have hell0 : 0 < ell := by have := R.hell; omega
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  set ρ := rhoM0 ell k e q0 with hρ
  set δ := δS ell ρ with hδ
  have hδ1 : δ < 1 := δS_lt ell k Lu U a t e q0 R
  have hδ0 : 0 ≤ δ := δS_nonneg ell k Lu U a t e q0 R
  have ha := R.ha
  have he0 := R.he0
  have hρ0 : 0 ≤ ρ := m0_rho_nonneg ell k Lu U a t e q0 R
  set sn := Real.sqrt n with hsn
  have hsn0 : 0 < sn := Real.sqrt_pos.mpr hnpos
  have hsn2 : sn ^ 2 = n := Real.sq_sqrt hnpos.le
  set s := Real.sqrt (a * n ^ 3) with hs
  have hseq : s = Real.sqrt a * (n * sn) := by
    rw [hs, Real.sqrt_mul ha.le, sqrt_cube n hnpos.le]
  have hs0 : 0 < s := by rw [hseq]; have := Real.sqrt_pos.mpr ha; positivity
  have hcoS : ∀ v, (1 - δ) * ‖v‖ ^ 2 ≤ ⟪v, Sop ell k Lu U a t e q0 R v⟫ := Sop_coer ell k Lu U a t e q0 R H
  have h1δ : 0 < 1 - δ := by linarith
  set w := Ring.inverse (Sop ell k Lu U a t e q0 R) (s⁻¹ • u) with hw
  have hSw : Sop ell k Lu U a t e q0 R w = s⁻¹ • u := coercive_apply_inverse _ h1δ hcoS _
  have hwb : (1 - δ) * ‖w‖ ≤ ‖s⁻¹ • u‖ := coercive_inv_bound _ h1δ hcoS _
  set g := Eop ell k Lu hell0 w with hg
  -- the master size: m = n √n ‖w‖ ≤ A0 ‖u‖
  have hA0 : A0S a δ = 1 / ((1 - δ) * Real.sqrt a) := rfl
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hm : n * sn * ‖w‖ ≤ A0S a δ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, hseq] at hwb
    rw [hA0, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have : (1 - δ) * ‖w‖ * (Real.sqrt a * (n * sn)) ≤ ‖u‖ := by
      have h2 := mul_le_mul_of_nonneg_right hwb (by positivity : (0 : ℝ) ≤ Real.sqrt a * (n * sn))
      rwa [inv_mul_eq_div, div_mul_cancel₀ _ (by positivity)] at h2
    nlinarith
  have hA0pos : 0 ≤ A0S a δ := by rw [hA0]; positivity
  -- sizes of g
  have hgn : ‖g‖ ≤ (81 / 4) * (n * sn * ‖w‖) := by
    have := Eop_norm ell k Lu hell0 w
    rw [sqrt_cube n hnpos.le] at this
    linarith
  have hΓ : ∀ ν, gradE g ν ≤ (648 * sn * ‖w‖) ^ 2 := by
    intro ν
    have := Eop_grad ell k Lu hell0 w ν
    rw [show (648 * sn * ‖w‖) ^ 2 = 419904 * sn ^ 2 * ‖w‖ ^ 2 by ring, hsn2]
    exact this
  have hΓ0 : 0 ≤ 648 * sn * ‖w‖ := by positivity
  have hcurl1 : ‖curlC (trivialU _) g‖ ≤ 6 * (648 * sn * ‖w‖) := by
    have h := curl_flat_le g _ hΓ
    have h2 : ‖curlC (trivialU _) g‖ ^ 2 ≤ (6 * (648 * sn * ‖w‖)) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  have hdiv1 : ‖ContinuousLinearMap.adjoint (gradL2 (trivialU _)) g‖ ≤ 3 * (648 * sn * ‖w‖) := by
    have h := div_flat_le g _ hΓ
    rwa [Real.sqrt_sq hΓ0] at h
  have hcurl : ‖curlC U g‖ ≤ 6 * (648 * sn * ‖w‖) + 12 * e * ‖g‖ := by
    have h := curl_cov_diff U e R.hlinks g
    have : ‖curlC U g‖ ≤ ‖curlC (trivialU _) g‖ + ‖curlC U g - curlC (trivialU _) g‖ := by
      have e1 : curlC U g = curlC (trivialU _) g + (curlC U g - curlC (trivialU _) g) := by abel
      conv_lhs => rw [e1]
      exact norm_add_le _ _
    linarith
  have hdiv : ‖ContinuousLinearMap.adjoint (gradL2 U) g‖ ≤ 3 * (648 * sn * ‖w‖) + 2 * Real.sqrt 3 * e * ‖g‖ := by
    have h := div_cov_diff U e R.hlinks g
    have : ‖ContinuousLinearMap.adjoint (gradL2 U) g‖ ≤ ‖ContinuousLinearMap.adjoint (gradL2 (trivialU _)) g‖
        + ‖ContinuousLinearMap.adjoint (gradL2 U) g - ContinuousLinearMap.adjoint (gradL2 (trivialU _)) g‖ := by
      have e1 : ContinuousLinearMap.adjoint (gradL2 U) g = ContinuousLinearMap.adjoint (gradL2 (trivialU _)) g
          + (ContinuousLinearMap.adjoint (gradL2 U) g - ContinuousLinearMap.adjoint (gradL2 (trivialU _)) g) := by abel
      conv_lhs => rw [e1]
      exact norm_add_le _ _
    linarith
  have hne := m0_ne_le ell k Lu U a t e q0 R
  -- the scaled quantities
  set I := ginvM0 ell k Lu U a t e q0 R φ θ hφ hc H with hI
  have hIC : ∀ v, I.C v = n • curlC U v := fun v => rfl
  have hID : ∀ v, ContinuousLinearMap.adjoint I.D v = n • ContinuousLinearMap.adjoint (gradL2 U) v := by
    intro v
    show ContinuousLinearMap.adjoint (n • gradL2 U) v = _
    rw [adjoint_smul_real, ContinuousLinearMap.smul_apply]
  have hIQ : I.Qb g = u := by
    show (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull) g = u
    rw [ContinuousLinearMap.smul_apply]
    have e2 : (bondSectorOf (GF ell k Lu) U).Qfull g = Sop ell k Lu U a t e q0 R w := rfl
    rw [e2, hSw, smul_smul, ← hs, mul_inv_cancel₀ hs0.ne', one_smul]
  refine ⟨g, hIQ, ?_⟩
  have hup := I.Ginv_upper g
  have hκ : I.κ = κS ρ := rfl
  have hc' : I.c = cS a ρ := rfl
  have hν : I.ν = νS ρ := rfl
  have hM : I.M = 1 := rfl
  rw [hκ, hc', hν, hM, hIQ, one_mul] at hup
  have hcS := hc.cS_pos
  have hκS := hc.κS_nonneg
  have hνS := hc.νS_nonneg
  -- the three first-order sizes
  have hXC : ‖I.C g‖ ≤ cNS a ρ δ * ‖u‖ := by
    rw [hIC, norm_smul, Real.norm_eq_abs, abs_of_pos hnpos]
    have h1 : n * ‖curlC U g‖ ≤ n * (6 * (648 * sn * ‖w‖) + 12 * e * ‖g‖) :=
      mul_le_mul_of_nonneg_left hcurl hnpos.le
    have h2 : n * (6 * (648 * sn * ‖w‖) + 12 * e * ‖g‖) = 3888 * (n * sn * ‖w‖) + 12 * (n * e) * ‖g‖ := by ring
    have h3 : 12 * (n * e) * ‖g‖ ≤ 12 * ρ * ((81 / 4) * (n * sn * ‖w‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hne (by norm_num)) hgn (norm_nonneg _) (by positivity)
    have h4 : 3888 * (n * sn * ‖w‖) + 12 * ρ * ((81 / 4) * (n * sn * ‖w‖)) = (3888 + 243 * ρ) * (n * sn * ‖w‖) := by ring
    have h5 : (3888 + 243 * ρ) * (n * sn * ‖w‖) ≤ (3888 + 243 * ρ) * (A0S a δ * ‖u‖) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    unfold cNS
    nlinarith
  have hXD : ‖ContinuousLinearMap.adjoint I.D g‖ ≤ dNS a ρ δ * ‖u‖ := by
    rw [hID, norm_smul, Real.norm_eq_abs, abs_of_pos hnpos]
    have h1 : n * ‖ContinuousLinearMap.adjoint (gradL2 U) g‖ ≤ n * (3 * (648 * sn * ‖w‖) + 2 * Real.sqrt 3 * e * ‖g‖) :=
      mul_le_mul_of_nonneg_left hdiv hnpos.le
    have h2 : n * (3 * (648 * sn * ‖w‖) + 2 * Real.sqrt 3 * e * ‖g‖)
        = 1944 * (n * sn * ‖w‖) + 2 * Real.sqrt 3 * (n * e) * ‖g‖ := by ring
    have h3 : 2 * Real.sqrt 3 * (n * e) * ‖g‖ ≤ 2 * Real.sqrt 3 * ρ * ((81 / 4) * (n * sn * ‖w‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hne (by positivity)) hgn (norm_nonneg _) (by positivity)
    have h4 : 1944 * (n * sn * ‖w‖) + 2 * Real.sqrt 3 * ρ * ((81 / 4) * (n * sn * ‖w‖))
        = (1944 + (81 * Real.sqrt 3 / 2) * ρ) * (n * sn * ‖w‖) := by ring
    have h5 : (1944 + (81 * Real.sqrt 3 / 2) * ρ) * (n * sn * ‖w‖) ≤ (1944 + (81 * Real.sqrt 3 / 2) * ρ) * (A0S a δ * ‖u‖) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    unfold dNS
    nlinarith
  have hXg : ‖g‖ ≤ gNS a δ * ‖u‖ := by
    unfold gNS
    have := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 81 / 4)
    nlinarith
  -- assemble
  set uu := ‖u‖ with huu
  have huu0 : 0 ≤ uu := norm_nonneg _
  have hY1 : ‖I.C g‖ + κS ρ * (‖ContinuousLinearMap.adjoint I.D g‖ / cS a ρ)
      ≤ (cNS a ρ δ + κS ρ * (dNS a ρ δ / cS a ρ)) * uu := by
    have h1 : ‖ContinuousLinearMap.adjoint I.D g‖ / cS a ρ ≤ dNS a ρ δ * uu / cS a ρ :=
      div_le_div_of_nonneg_right hXD hcS.le
    have h2 := mul_le_mul_of_nonneg_left h1 hκS
    have e1 : (cNS a ρ δ + κS ρ * (dNS a ρ δ / cS a ρ)) * uu = cNS a ρ δ * uu + κS ρ * (dNS a ρ δ * uu / cS a ρ) := by
      field_simp
    rw [e1]; linarith
  have hY2 : ‖g‖ + ‖ContinuousLinearMap.adjoint I.D g‖ / Real.sqrt (cS a ρ)
      ≤ (gNS a δ + dNS a ρ δ / Real.sqrt (cS a ρ)) * uu := by
    have h1 : ‖ContinuousLinearMap.adjoint I.D g‖ / Real.sqrt (cS a ρ) ≤ dNS a ρ δ * uu / Real.sqrt (cS a ρ) :=
      div_le_div_of_nonneg_right hXD (Real.sqrt_nonneg _)
    have hsc : 0 < Real.sqrt (cS a ρ) := Real.sqrt_pos.mpr hcS
    have e1 : (gNS a δ + dNS a ρ δ / Real.sqrt (cS a ρ)) * uu = gNS a δ * uu + dNS a ρ δ * uu / Real.sqrt (cS a ρ) := by
      field_simp
    rw [e1]; linarith
  have hL1 : 0 ≤ ‖I.C g‖ + κS ρ * (‖ContinuousLinearMap.adjoint I.D g‖ / cS a ρ) := by positivity
  have hL2 : 0 ≤ ‖g‖ + ‖ContinuousLinearMap.adjoint I.D g‖ / Real.sqrt (cS a ρ) := by positivity
  have hq1 := pow_le_pow_left₀ hL1 hY1 2
  have hq2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL2 hY2 2) hνS
  have hq3 := pow_le_pow_left₀ (norm_nonneg _) hXD 2
  refine hup.trans ?_
  calc (‖I.C g‖ + κS ρ * (‖ContinuousLinearMap.adjoint I.D g‖ / cS a ρ)) ^ 2
        + νS ρ * (‖g‖ + ‖ContinuousLinearMap.adjoint I.D g‖ / Real.sqrt (cS a ρ)) ^ 2
        + ‖ContinuousLinearMap.adjoint I.D g‖ ^ 2 + uu ^ 2
      ≤ ((cNS a ρ δ + κS ρ * (dNS a ρ δ / cS a ρ)) * uu) ^ 2
        + νS ρ * ((gNS a δ + dNS a ρ δ / Real.sqrt (cS a ρ)) * uu) ^ 2
        + (dNS a ρ δ * uu) ^ 2 + uu ^ 2 := by linarith [hq1, hq2, hq3]
    _ = bNS a ρ δ * uu ^ 2 := by unfold bNS; ring

end

#print axioms sqrt_cube
#print axioms m0_ne_le
#print axioms bondExtM0

end AdalyFormal.DLayer
