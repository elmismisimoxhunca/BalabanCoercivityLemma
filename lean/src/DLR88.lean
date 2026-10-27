import DLR87

/-!
# DL88 -- numerics, part 4: **`m0ClassNum_two : M0ClassNum 2 1 1 ρ β θ₀`** for `0 ≤ ρ ≤ 10⁻¹³⁰`, `0 ≤ β ≤ 10⁻²⁵⁰`,
and the conclusion constant is positive: **`gam0_two_pos`** : `9·10⁻⁵ ≤ gam0M0f 2 1 1 ρ ε' εJ (dCM0 2 ρ) (cBM0 2 ρ)`.

Composite bounds: `(1/θ₀+2)^{3/2} ≤ 3.18·10⁶⁷`, `CHfree ≤ 10⁷⁹`, `K2s 2 ≤ 8.653·10¹⁰`, `K2free ≤ 5·10¹¹`, `JSfree β ≤ β`,
`νψ ≤ 10⁹¹β`, `δψ ≤ νψ`, `cg1 ≥ 2.4·10⁻⁴`, `bN1 ≤ 2·10⁷`, `EN1free ≤ 10⁻¹²`, `CH1free ≤ 10⁷⁹`, `KDfree 2 ≤ 7·10¹¹`,
`ε' ≤ 10⁹⁵β`, `εJ ≤ 10⁹¹β`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open AdalyFormal.AsmM0 (Mc KhatM0 phiC)
open AdalyFormal.BondComposite (rr)
open AdalyFormal.RegBgKU (kapHat)
open AdalyFormal.NonflatJet (rhoOf)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.M0Finish (dCM0 cBM0)

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

theorem Xθ_le : (1 / θ₀ + 2) * Real.sqrt (1 / θ₀ + 2) ≤ 3.18e67 := by
  rw [one_div_one_div]
  have hs : Real.sqrt ((10 : ℝ) ^ 45 + 2) ≤ 3.17e22 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  calc ((10 : ℝ) ^ 45 + 2) * Real.sqrt ((10 : ℝ) ^ 45 + 2) ≤ ((10 : ℝ) ^ 45 + 2) * 3.17e22 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 3.18e67 := by norm_num

theorem Xθ_nn : 0 ≤ (1 / θ₀ + 2) * Real.sqrt (1 / θ₀ + 2) := by positivity

theorem K2s_two_le : K2s 2 ≤ 8.653e10 := by
  unfold K2s
  have h3 := sqrt3_le'
  push_cast
  nlinarith

theorem K2s_two_nn : 0 ≤ K2s 2 := by unfold K2s; positivity

theorem KDfree_two_le : KDfree 2 ≤ 7e11 := by
  unfold KDfree
  have := K2s_two_le
  push_cast
  nlinarith

/-- `e2Majorant ∘ rhoOf 2` is linear near `0` -/
theorem e2rho_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 1000) : e2Majorant (rhoOf 2 x) ≤ 231 * x := by
  have hr := AdalyFormal.NonflatJet.rhoOf_le (ell := 2) x h0
  push_cast at hr
  have hr0 : 0 ≤ rhoOf 2 x := by unfold AdalyFormal.NonflatJet.rhoOf; positivity
  have hr1 : rhoOf 2 x ≤ 1 / 10 := by linarith
  have he := AdalyFormal.NonflatJet.e2Majorant_le_twelve hr0 hr1
  linarith

theorem JSfree_le (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1 / 10 ^ 5) : JSfree β ≤ β := by
  unfold JSfree
  have hs2 : (1.41 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hb1 : β ≤ 1 := h1.trans (by norm_num)
  have p2 : β ^ 2 ≤ β * (1 / 10 ^ 5) := by rw [pow_two]; exact mul_le_mul_of_nonneg_left h1 h0
  have p3 : β ^ 3 ≤ β ^ 2 := by
    rw [show β ^ 3 = β ^ 2 * β by ring]; exact mul_le_of_le_one_right (sq_nonneg β) hb1
  have p4 : β ^ 4 ≤ β ^ 3 := by
    rw [show β ^ 4 = β ^ 3 * β by ring]; exact mul_le_of_le_one_right (by positivity) hb1
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hs2 h0
  nlinarith

section
variable (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130)

include h0 h1 in
theorem hK2c_two : 1536 * ((2 : ℕ) : ℝ) ^ 2 * e2Majorant (rhoOf 2 ρ) < 1 - 1 / ((2 : ℕ) : ℝ) := by
  have := e2rho_le ρ h0 (h1.trans (by norm_num))
  push_cast
  nlinarith

include h0 h1 in
theorem thetaK2_two : thetaK2 2 ρ ≤ 0.5001 := by
  unfold thetaK2
  have := e2rho_le ρ h0 (h1.trans (by norm_num))
  push_cast
  nlinarith

include h0 h1 in
theorem hKDc_two :
    192 * (8 * ((2 : ℕ) : ℝ) * kapHat 2 ρ + 8 * e2Majorant (rhoOf 2 (kapHat 2 ρ))) ≤ 1 / (2 * ((2 : ℕ) : ℝ) ^ 3) := by
  have hk := AdalyFormal.M0Finish.kapHat_two_le ρ h0 (h1.trans (by norm_num))
  have hk0 : 0 ≤ kapHat 2 ρ := by
    unfold AdalyFormal.RegBgKU.kapHat; have := AdalyFormal.RegBgKU.Kc_pos 2 le_rfl; positivity
  have hk1 : kapHat 2 ρ ≤ 1 / 1000 := by nlinarith
  have he := e2rho_le (kapHat 2 ρ) hk0 hk1
  push_cast
  nlinarith

include h0 h1 in
theorem K2free_two : 0 ≤ K2free 2 ρ ∧ K2free 2 ρ ≤ 5e11 := by
  have hθ := thetaK2_two ρ h0 h1
  have hden : 0 < 1 - thetaK2 2 ρ := by linarith
  have hE := exp_drift2_le ρ h0 h1
  have hE0 := (Real.exp_pos (2 * (3600 * ((2 : ℕ) : ℝ) * ρ) / rr 2)).le
  have hK := K2s_two_le
  have hK0 := K2s_two_nn
  unfold K2free
  constructor
  · apply div_nonneg _ hden.le; positivity
  · rw [div_le_iff₀ hden]
    have : K2s 2 * Real.exp (2 * (3600 * ((2 : ℕ) : ℝ) * ρ) / rr 2) ≤ 8.653e10 * 1.0001 :=
      mul_le_mul hK hE hE0 (by norm_num)
    push_cast at this ⊢
    nlinarith

variable (hK : 0 < KhatM0 2 1 1 ρ) (hc : CondM0 2 1 ρ θ₀) (hEG : 4 * EGM0 2 1 ρ θ₀ hc ≤ 1 / KhatM0 2 1 1 ρ)

include h0 h1 in
theorem CHfree_two : 0 ≤ CHfree 2 1 1 ρ θ₀ hc hK hEG ∧ CHfree 2 1 1 ρ θ₀ hc hK hEG ≤ 1e79 := by
  obtain ⟨hEN, hENl⟩ := ENfree_two ρ h0 h1 hK hEG
  have hbN := bNS_two ρ h0 h1
  have hbN0 := bNS_two_pos ρ h0 h1
  obtain ⟨-, hKl⟩ := KhatM0_two ρ h0 h1 h1
  obtain ⟨hq0, hq⟩ := qBS_two ρ h0 h1
  have hB := δBS_two ρ h0 h1
  have hB0 := hc.δBS_nonneg
  have hinv : 1 / (1.9e7 : ℝ) ≤ 1 / bNS 1 ρ (δS 2 ρ) := one_div_le_one_div_of_le hbN0 hbN
  have hD : (5.2e-8 : ℝ) ≤ 1 / bNS 1 ρ (δS 2 ρ) - ENfree 2 1 1 ρ θ₀ hc hK hEG := by
    have : (5.2e-8 : ℝ) + 1 / 10 ^ 12 ≤ 1 / 1.9e7 := by norm_num
    linarith
  have hD0 : 0 < 1 / bNS 1 ρ (δS 2 ρ) - ENfree 2 1 1 ρ θ₀ hc hK hEG := lt_of_lt_of_le (by norm_num) hD
  have hnum : 2 * KhatM0 2 1 1 ρ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀) ≤ 8002 * 1.03 := by
    have : qBS 2 1 ρ + δBS 2 1 ρ θ₀ ≤ 1.03 := by
      have : 200 * θ₀ ≤ 0.01 := by norm_num
      linarith
    exact mul_le_mul (by linarith) this (by positivity) (by norm_num)
  have hnum0 : 0 ≤ 2 * KhatM0 2 1 1 ρ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀) := by positivity
  have hY : 2 * KhatM0 2 1 1 ρ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
      / (1 / bNS 1 ρ (δS 2 ρ) - ENfree 2 1 1 ρ θ₀ hc hK hEG) ≤ 1.6e11 := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hY0 : 0 ≤ 2 * KhatM0 2 1 1 ρ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
      / (1 / bNS 1 ρ (δS 2 ρ) - ENfree 2 1 1 ρ θ₀ hc hK hEG) := div_nonneg hnum0 hD0.le
  have hX := Xθ_le
  have hX0 := Xθ_nn
  have h3 := sqrt3_le'
  have h30 := Real.sqrt_nonneg 3
  unfold CHfree
  rw [Real.sqrt_one, mul_one]
  constructor
  · positivity
  · calc Real.sqrt 3 * ((1 / θ₀ + 2) * Real.sqrt (1 / θ₀ + 2))
          * (2 * KhatM0 2 1 1 ρ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
            / (1 / bNS 1 ρ (δS 2 ρ) - ENfree 2 1 1 ρ θ₀ hc hK hEG))
        ≤ 1.7321 * 3.18e67 * 1.6e11 := mul_le_mul (mul_le_mul h3 hX hX0 (by norm_num)) hY hY0 (by positivity)
      _ ≤ 1e79 := by norm_num

variable (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)

include h0 h1 hβ0 hβ1 in
theorem nuPsi_two : 0 ≤ nuPsi 2 1 1 ρ β θ₀ hc hK hEG ∧ nuPsi 2 1 1 ρ β θ₀ hc hK hEG ≤ 1 / 10 ^ 159 := by
  obtain ⟨hC0, hC⟩ := CHfree_two ρ h0 h1 hK hc hEG
  obtain ⟨hK20, hK2⟩ := K2free_two ρ h0 h1
  have hJ := JSfree_le β hβ0 (hβ1.trans (by norm_num))
  have hJ0 := JSfree_nonneg β hβ0
  unfold nuPsi
  constructor
  · positivity
  · calc 2 * CHfree 2 1 1 ρ θ₀ hc hK hEG * JSfree β * K2free 2 ρ ≤ 2 * 1e79 * (1 / 10 ^ 250) * 5e11 :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num)) (hJ.trans hβ1) hJ0 (by positivity))
            hK2 hK20 (by positivity)
      _ ≤ 1 / 10 ^ 159 := by norm_num

include h0 h1 hβ0 hβ1 in
theorem deltaPsi_two : 0 ≤ deltaPsi 2 1 1 ρ β θ₀ hc hK hEG ∧
    deltaPsi 2 1 1 ρ β θ₀ hc hK hEG ≤ 1 / 10 ^ 159 := by
  obtain ⟨hn0, hn⟩ := nuPsi_two ρ β h0 h1 hK hc hEG hβ0 hβ1
  have h5 := e5θ_le
  have h50 := expm1_nn 5 (by norm_num)
  have hp : (Real.exp (5 * θ₀) - 1) * (Real.exp (5 * θ₀) + 1) ≤ (6 * θ₀) * 3 :=
    mul_le_mul h5 (by have : 6 * θ₀ ≤ 1 := by norm_num
                      linarith) (by linarith) (by positivity)
  have hp0 : 0 ≤ (Real.exp (5 * θ₀) - 1) * (Real.exp (5 * θ₀) + 1) := mul_nonneg h50 (by linarith)
  unfold deltaPsi
  constructor
  · positivity
  · have : nuPsi 2 1 1 ρ β θ₀ hc hK hEG * 648 * ((Real.exp (5 * θ₀) - 1) * (Real.exp (5 * θ₀) + 1))
        ≤ nuPsi 2 1 1 ρ β θ₀ hc hK hEG * 648 * ((6 * θ₀) * 3) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    have h2 : nuPsi 2 1 1 ρ β θ₀ hc hK hEG * 648 * ((6 * θ₀) * 3) ≤ nuPsi 2 1 1 ρ β θ₀ hc hK hEG := by
      have : (648 : ℝ) * ((6 * θ₀) * 3) ≤ 1 := by norm_num
      nlinarith
    linarith

end

section
variable (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hc : CondM0 2 1 ρ θ₀)
  (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ) (hν1 : νψ ≤ 1 / 10 ^ 150) (hδ1 : δψ ≤ 1 / 10 ^ 150)

include h0 h1 hν1 hδ1 in
/-- **the perturbed model `G₁⁻¹` structure is in the DL86 small regime** -/
theorem ginv1Small_two : GinvSmall (hc.ginv1 νψ δψ hν hδ) where
  gam := (ginvSmall_two ρ h0 h1).gam
  hδC := (ginvSmall_two ρ h0 h1).hδC
  hκ := (ginvSmall_two ρ h0 h1).hκ
  hδK := (ginvSmall_two ρ h0 h1).hδK
  hν := by
    show νS ρ + νψ ≤ 1 / 10 ^ 100
    have := νS_le ρ h0 h1
    have : 816 * ρ ≤ 816 / 10 ^ 130 := by nlinarith
    have : (816 : ℝ) / 10 ^ 130 + 1 / 10 ^ 150 ≤ 1 / 10 ^ 100 := by norm_num
    linarith
  hδν := by
    show δνS ρ θ₀ + δψ ≤ 1 / 10 ^ 100
    have := δνS_le ρ h0 h1
    have : 816 * ρ ≤ 816 / 10 ^ 130 := by nlinarith
    have : (816 : ℝ) / 10 ^ 130 + 1 / 10 ^ 150 ≤ 1 / 10 ^ 100 := by norm_num
    linarith
  hδB := (ginvSmall_two ρ h0 h1).hδB
  hM := rfl

include h0 h1 hν1 in
theorem cg1_two : (2.4e-4 : ℝ) ≤ cg1 2 1 1 ρ θ₀ hc νψ := by
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have hi := one_div_le_one_div_of_le hK hKl
  have hW := (ginvSmall_two ρ h0 h1).nW_le
  have hW0 := (ginvSmall_two ρ h0 h1).nW_nonneg'
  have hW2 : hc.ginv.nW ^ 2 ≤ (4e12) ^ 2 := pow_le_pow_left₀ hW0 hW 2
  have hp : νψ * hc.ginv.nW ^ 2 ≤ (1 / 10 ^ 150) * (4e12) ^ 2 := mul_le_mul hν1 hW2 (sq_nonneg _) (by positivity)
  unfold cg1
  have : (2.4e-4 : ℝ) + (1 / 10 ^ 150) * (4e12) ^ 2 ≤ 1 / 4001 := by norm_num
  linarith

include h0 h1 hν hν1 in
theorem bN1_two : bN1 2 1 1 ρ θ₀ hc νψ ≤ 2e7 := by
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have hW := (ginvSmall_two ρ h0 h1).nW_le
  have hW0 := (ginvSmall_two ρ h0 h1).nW_nonneg'
  have hW2 : hc.ginv.nW ^ 2 ≤ (4e12) ^ 2 := pow_le_pow_left₀ hW0 hW 2
  have hp : νψ * hc.ginv.nW ^ 2 * KhatM0 2 1 1 ρ ≤ (1 / 10 ^ 150) * (4e12) ^ 2 * 4001 :=
    mul_le_mul (mul_le_mul hν1 hW2 (sq_nonneg _) (by positivity)) hKl hK.le (by positivity)
  have hp0 : 0 ≤ νψ * hc.ginv.nW ^ 2 * KhatM0 2 1 1 ρ := by positivity
  have hb := bNS_two ρ h0 h1
  have hb0 := (bNS_two_pos ρ h0 h1).le
  unfold bN1
  calc bNS 1 ρ (δS 2 ρ) * (1 + νψ * hc.ginv.nW ^ 2 * KhatM0 2 1 1 ρ)
      ≤ 1.9e7 * (1 + (1 / 10 ^ 150) * (4e12) ^ 2 * 4001) := mul_le_mul hb (by linarith) (by positivity) (by norm_num)
    _ ≤ 2e7 := by norm_num

variable (hK : 0 < KhatM0 2 1 1 ρ) (hcg : 0 < cg1 2 1 1 ρ θ₀ hc νψ)
  (hEG1 : 4 * EGM1 2 1 ρ θ₀ hc νψ δψ hν hδ ≤ cg1 2 1 1 ρ θ₀ hc νψ)

include h0 h1 hν1 hδ1 in
/-- **the model Schur structure of `EN1free` is in the DL86 small regime** -/
theorem n1Small_two : NSmall (modelNOf (hc.ginv1 νψ δψ hν hδ) (cg1 2 1 1 ρ θ₀ hc νψ) (qBS 2 1 ρ) (bN1 2 1 1 ρ θ₀ hc νψ)
    hcg hEG1 (qBS_two ρ h0 h1).1 (bN1_pos 2 1 1 ρ θ₀ hc νψ hν hK)) where
  ginv := ginv1Small_two ρ h0 h1 hc νψ δψ hν hδ hν1 hδ1
  hcg := cg1_two ρ h0 h1 hc νψ hν1
  hqb := (qBS_two ρ h0 h1).2
  hbN := bN1_two ρ h0 h1 hc νψ hν hν1

include h0 h1 hν1 hδ1 in
theorem EN1free_two : EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 ≤ 1 / 10 ^ 12 ∧
    EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 < 1 / bN1 2 1 1 ρ θ₀ hc νψ :=
  ⟨(n1Small_two ρ h0 h1 hc νψ δψ hν hδ hν1 hδ1 hK hcg hEG1).EN_le,
    (n1Small_two ρ h0 h1 hc νψ δψ hν hδ hν1 hδ1 hK hcg hEG1).EN_lt⟩

include h0 h1 hν1 hδ1 in
theorem CH1free_two : 0 ≤ CH1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 ∧
    CH1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 ≤ 1e79 := by
  obtain ⟨hEN, hENl⟩ := EN1free_two ρ h0 h1 hc νψ δψ hν hδ hν1 hδ1 hK hcg hEG1
  have hbN := bN1_two ρ h0 h1 hc νψ hν hν1
  have hbN0 := bN1_pos 2 1 1 ρ θ₀ hc νψ hν hK
  have hcg1 := cg1_two ρ h0 h1 hc νψ hν1
  obtain ⟨hq0, hq⟩ := qBS_two ρ h0 h1
  have hB := δBS_two ρ h0 h1
  have hB0 := hc.δBS_nonneg
  have hinv : 1 / (2e7 : ℝ) ≤ 1 / bN1 2 1 1 ρ θ₀ hc νψ := one_div_le_one_div_of_le hbN0 hbN
  have hD : (4.99e-8 : ℝ) ≤ 1 / bN1 2 1 1 ρ θ₀ hc νψ - EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 := by
    have : (4.99e-8 : ℝ) + 1 / 10 ^ 12 ≤ 1 / 2e7 := by norm_num
    linarith
  have hD0 : 0 < 1 / bN1 2 1 1 ρ θ₀ hc νψ - EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1 :=
    lt_of_lt_of_le (by norm_num) hD
  have h2c : 2 / cg1 2 1 1 ρ θ₀ hc νψ ≤ 2 / 2.4e-4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hcg1
  have hnum : 2 / cg1 2 1 1 ρ θ₀ hc νψ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀) ≤ (2 / 2.4e-4) * 1.03 := by
    have : qBS 2 1 ρ + δBS 2 1 ρ θ₀ ≤ 1.03 := by
      have : 200 * θ₀ ≤ 0.01 := by norm_num
      linarith
    exact mul_le_mul h2c this (by positivity) (by norm_num)
  have hnum0 : 0 ≤ 2 / cg1 2 1 1 ρ θ₀ hc νψ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀) := by positivity
  have hY : 2 / cg1 2 1 1 ρ θ₀ hc νψ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
      / (1 / bN1 2 1 1 ρ θ₀ hc νψ - EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1) ≤ 1.73e11 := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hY0 : 0 ≤ 2 / cg1 2 1 1 ρ θ₀ hc νψ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
      / (1 / bN1 2 1 1 ρ θ₀ hc νψ - EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1) := div_nonneg hnum0 hD0.le
  have hX := Xθ_le
  have hX0 := Xθ_nn
  have h3 := sqrt3_le'
  have h30 := Real.sqrt_nonneg 3
  unfold CH1free
  rw [Real.sqrt_one, mul_one]
  constructor
  · positivity
  · calc Real.sqrt 3 * ((1 / θ₀ + 2) * Real.sqrt (1 / θ₀ + 2))
          * (2 / cg1 2 1 1 ρ θ₀ hc νψ * (qBS 2 1 ρ + δBS 2 1 ρ θ₀)
            / (1 / bN1 2 1 1 ρ θ₀ hc νψ - EN1free 2 1 1 ρ θ₀ hc νψ δψ hν hδ hK hcg hEG1))
        ≤ 1.7321 * 3.18e67 * 1.73e11 := mul_le_mul (mul_le_mul h3 hX hX0 (by norm_num)) hY hY0 (by positivity)
      _ ≤ 1e79 := by norm_num

end

/-- **THE NUMERICS PACKAGE IS INHABITED** at `ℓ = 2`, `a = t = 1`, `θ = 10⁻⁴⁵`, every `0 ≤ ρ ≤ 10⁻¹³⁰`, `0 ≤ β ≤ 10⁻²⁵⁰` -/
theorem m0ClassNum_two (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250) :
    M0ClassNum 2 1 1 ρ β θ₀ := by
  have hc := condM0_two ρ h0 h1
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have hEG := hEG_two ρ h0 h1
  obtain ⟨-, hN⟩ := ENfree_two ρ h0 h1 hK hEG
  obtain ⟨hν, hν1⟩ := nuPsi_two ρ β h0 h1 hK hc hEG hβ0 hβ1
  obtain ⟨hδ, hδ1⟩ := deltaPsi_two ρ β h0 h1 hK hc hEG hβ0 hβ1
  have hν2 : nuPsi 2 1 1 ρ β θ₀ hc hK hEG ≤ 1 / 10 ^ 150 := hν1.trans (by norm_num)
  have hδ2 : deltaPsi 2 1 1 ρ β θ₀ hc hK hEG ≤ 1 / 10 ^ 150 := hδ1.trans (by norm_num)
  have hcg1 := cg1_two ρ h0 h1 hc _ hν2
  have hcg1p : 0 < cg1 2 1 1 ρ θ₀ hc (nuPsi 2 1 1 ρ β θ₀ hc hK hEG) := lt_of_lt_of_le (by norm_num) hcg1
  have hEG1 : 4 * EGM1 2 1 ρ θ₀ hc (nuPsi 2 1 1 ρ β θ₀ hc hK hEG) (deltaPsi 2 1 1 ρ β θ₀ hc hK hEG) hν hδ
      ≤ cg1 2 1 1 ρ θ₀ hc (nuPsi 2 1 1 ρ β θ₀ hc hK hEG) := by
    have := (ginv1Small_two ρ h0 h1 hc _ _ hν hδ hν2 hδ2).EG_le
    have : 4 * (1 / 10 ^ 36 : ℝ) ≤ 2.4e-4 := by norm_num
    unfold EGM1
    linarith
  obtain ⟨-, hN1⟩ := EN1free_two ρ h0 h1 hc _ _ hν hδ hν2 hδ2 hK hcg1p hEG1
  have hε' : 2 * CHfree 2 1 1 ρ θ₀ hc hK hEG * JSfree β * K2free 2 ρ * KhatM0 2 1 1 ρ < 1 := by
    have e : 2 * CHfree 2 1 1 ρ θ₀ hc hK hEG * JSfree β * K2free 2 ρ = nuPsi 2 1 1 ρ β θ₀ hc hK hEG := rfl
    rw [e]
    have := mul_le_mul hν1 hKl hK.le (by positivity)
    have : (1 / 10 ^ 159 : ℝ) * 4001 < 1 := by norm_num
    linarith
  exact ⟨by positivity, hβ0, hc, hK, hEG, hN, hK2c_two ρ h0 h1, hKDc_two ρ h0 h1, hν, hδ, hcg1p, hEG1, hN1, hε'⟩

theorem eps2free_two (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)
    (Num : M0ClassNum 2 1 1 ρ β θ₀) : 0 ≤ eps2free Num ∧ eps2free Num ≤ 1 / 10 ^ 155 := by
  obtain ⟨hν, hν1⟩ := nuPsi_two ρ β h0 h1 Num.hK Num.hc Num.hEG hβ0 hβ1
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have e : eps2free Num = nuPsi 2 1 1 ρ β θ₀ Num.hc Num.hK Num.hEG * KhatM0 2 1 1 ρ := rfl
  rw [e]
  refine ⟨mul_nonneg hν hK.le, ?_⟩
  have := mul_le_mul hν1 hKl hK.le (by positivity)
  have : (1 / 10 ^ 159 : ℝ) * 4001 ≤ 1 / 10 ^ 155 := by norm_num
  linarith

theorem epsJfree_two (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)
    (Num : M0ClassNum 2 1 1 ρ β θ₀) : 0 ≤ epsJfree Num ∧ epsJfree Num ≤ 1 / 10 ^ 159 := by
  obtain ⟨hν, hν1⟩ := nuPsi_two ρ β h0 h1 Num.hK Num.hc Num.hEG hβ0 hβ1
  obtain ⟨hδ, hδ1⟩ := deltaPsi_two ρ β h0 h1 Num.hK Num.hc Num.hEG hβ0 hβ1
  obtain ⟨hC0, hC⟩ := CH1free_two ρ h0 h1 Num.hc _ _ Num.hν Num.hδ (hν1.trans (by norm_num)) (hδ1.trans (by norm_num))
    Num.hK Num.hcg1 Num.hEG1
  have hJ := JSfree_le β hβ0 (hβ1.trans (by norm_num))
  have hJ0 := JSfree_nonneg β hβ0
  have hKD := KDfree_two_le
  have hKD0 := KDfree_nonneg 2
  unfold epsJfree
  refine ⟨by positivity, ?_⟩
  calc KDfree 2 * CH1free 2 1 1 ρ θ₀ Num.hc (nuPsi 2 1 1 ρ β θ₀ Num.hc Num.hK Num.hEG)
        (deltaPsi 2 1 1 ρ β θ₀ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 * JSfree β
      ≤ 7e11 * 1e79 * (1 / 10 ^ 250) :=
        mul_le_mul (mul_le_mul hKD hC hC0 (by norm_num)) (hJ.trans hβ1) hJ0 (by positivity)
    _ ≤ 1 / 10 ^ 159 := by norm_num

/-- **the conclusion constant is positive**: `γ₀ ≥ 9·10⁻⁵` (with MF10's `gam0Form_pos`) -/
theorem gam0_two_pos (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)
    (Num : M0ClassNum 2 1 1 ρ β θ₀) :
    9e-5 ≤ gam0M0f 2 1 1 ρ (eps2free Num) (epsJfree Num) (dCM0 2 ρ) (cBM0 2 ρ) := by
  have h14 : ρ ≤ 1e-14 := h1.trans (by norm_num)
  obtain ⟨e0, e1⟩ := eps2free_two ρ β h0 h1 hβ0 hβ1 Num
  obtain ⟨j0, j1⟩ := epsJfree_two ρ β h0 h1 hβ0 hβ1 Num
  obtain ⟨E0, E1⟩ := AdalyFormal.M0Finish.EbarM0_two_le ρ h0 h14
  obtain ⟨c0, c1⟩ := AdalyFormal.M0Finish.cBM0_two_le ρ h0 h14
  unfold gam0M0f
  exact AdalyFormal.M0Finish.gam0Form_pos _ _ _ _ _ e0 (e1.trans (by norm_num)) j0 (j1.trans (by norm_num)) E0 E1
    (AdalyFormal.M0Finish.dCM0_nn 2 ρ) (AdalyFormal.M0Finish.dCM0_two_le ρ h0 h14) c0 c1

#print axioms K2free_two
#print axioms CHfree_two
#print axioms CH1free_two
#print axioms m0ClassNum_two
#print axioms eps2free_two
#print axioms epsJfree_two
#print axioms gam0_two_pos

end AdalyFormal.DLayer
