import DLR86
import MF10

/-!
# DL87 -- numerics, part 3: the k-free MODEL parameters at `ℓ = 2`, `a = 1`, `θ = θ₀ = 10⁻⁴⁵`, `0 ≤ ρ ≤ 10⁻¹³⁰`

Elementary bounds (each from `Real.exp_bound'` / `sqrt` squeezes, no numerics as premises):
`1/7 ≤ cS ≤ 1/6`, `δDS ≤ 2θ₀`, `δQS ≤ 4θ₀`, `qS = 1`, `1 ≤ bS ≤ 105000`, `cGS ≥ 4.5·10⁻¹¹`, `δCS ≤ 7θ₀`,
`κS, δKS, νS, δνS ≤ 816ρ`, `δBS ≤ 200θ₀`, `qBS ≤ 1.02`, `δS ≤ 2.1·10⁻⁵`, `bNS ≤ 1.9·10⁷`;
hence **`condM0_two : CondM0 2 1 ρ θ₀`**, **`ginvSmall_two : GinvSmall (condM0_two ..).ginv`** (DL86 regime), so
`EGM0 ≤ 10⁻³⁶`, and **`nSmall_two`** (the Schur model of `ENfree` is in the DL86 `NSmall` regime) so `ENfree ≤ 10⁻¹²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open AdalyFormal.AsmM0 (Mc KhatM0 phiC Mc_one phiC_two_le phiC_two_nn)
open AdalyFormal.BondComposite (rr)

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

/-- `e^x ≤ 1 + x + x²` on `[0,1]` (`Real.exp_bound'`, two Taylor terms) -/
theorem exp_le_quad (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg x]

theorem exp_le_two (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10 ^ 40) : Real.exp x ≤ 1 + 2 * x := by
  have h := exp_le_quad x h0 (h1.trans (by norm_num))
  have : x ^ 2 ≤ x := by
    rw [pow_two]; exact mul_le_of_le_one_right h0 (h1.trans (by norm_num))
  linarith

theorem rr2_ge : (0.7 : ℝ) ≤ rr 2 := by
  unfold rr; apply Real.le_sqrt_of_sq_le; push_cast; norm_num

theorem rr2_pos : 0 < rr 2 := lt_of_lt_of_le (by norm_num) rr2_ge

/-- the drift exponent at `ℓ = 2` -/
theorem drift_small (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) :
    3600 * ((2 : ℕ) : ℝ) * ρ / rr 2 ≤ 1 / 10 ^ 120 ∧ 0 ≤ 3600 * ((2 : ℕ) : ℝ) * ρ / rr 2 := by
  have hr := rr2_ge
  have hr0 := rr2_pos
  refine ⟨?_, by positivity⟩
  rw [div_le_iff₀ hr0]
  push_cast
  nlinarith

theorem drift2_small (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) :
    2 * (3600 * ((2 : ℕ) : ℝ) * ρ) / rr 2 ≤ 1 / 10 ^ 120 ∧ 0 ≤ 2 * (3600 * ((2 : ℕ) : ℝ) * ρ) / rr 2 := by
  have hr := rr2_ge
  have hr0 := rr2_pos
  refine ⟨?_, by positivity⟩
  rw [div_le_iff₀ hr0]
  push_cast
  nlinarith

theorem exp_drift_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) :
    Real.exp (3600 * ((2 : ℕ) : ℝ) * ρ / rr 2) ≤ 1.0001 := by
  obtain ⟨d1, d0⟩ := drift_small ρ h0 h1
  have := exp_le_two _ d0 (d1.trans (by norm_num))
  linarith [show 2 * (3600 * ((2 : ℕ) : ℝ) * ρ / rr 2) ≤ 2 / 10 ^ 120 by linarith]

theorem exp_drift2_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) :
    Real.exp (2 * (3600 * ((2 : ℕ) : ℝ) * ρ) / rr 2) ≤ 1.0001 := by
  obtain ⟨d1, d0⟩ := drift2_small ρ h0 h1
  have := exp_le_two _ d0 (d1.trans (by norm_num))
  linarith

theorem eθ_le : Real.exp θ₀ ≤ 1 + 2 * θ₀ := exp_le_two _ (by positivity) (by norm_num)

theorem e2θ_le : Real.exp (2 * θ₀) - 1 ≤ 3 * θ₀ := by
  have := exp_le_quad (2 * θ₀) (by positivity) (by norm_num)
  nlinarith

theorem e3θ_le : Real.exp (3 * θ₀) - 1 ≤ 4 * θ₀ := by
  have := exp_le_quad (3 * θ₀) (by positivity) (by norm_num)
  nlinarith

theorem e5θ_le : Real.exp (5 * θ₀) - 1 ≤ 6 * θ₀ := by
  have := exp_le_quad (5 * θ₀) (by positivity) (by norm_num)
  nlinarith

theorem expm1_nn (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Real.exp (c * θ₀) - 1 := by
  have := Real.add_one_le_exp (c * θ₀)
  have : 0 ≤ c * θ₀ := by positivity
  linarith

theorem sqrt3_le' : Real.sqrt 3 ≤ 1.7321 := sqrt_le_of _ _ (by norm_num) (by norm_num)

theorem qS_one : qS 1 = 1 := by unfold qS; exact Real.sqrt_one

theorem δDS_le : δDS θ₀ ≤ 2 * θ₀ := by
  unfold δDS
  have h3 := sqrt3_le'
  have he := eθ_le
  have h1 : θ₀ * Real.exp θ₀ ≤ θ₀ * (1 + 2 * θ₀) := mul_le_mul_of_nonneg_left he (by positivity)
  have h0 : 0 ≤ θ₀ * Real.exp θ₀ := by positivity
  calc Real.sqrt 3 * (θ₀ * Real.exp θ₀) ≤ 1.7321 * (θ₀ * (1 + 2 * θ₀)) :=
        mul_le_mul h3 h1 h0 (by norm_num)
    _ ≤ 2 * θ₀ := by norm_num

theorem δDS_nn : 0 ≤ δDS θ₀ := by unfold δDS; positivity

theorem δQS_le : δQS 1 θ₀ ≤ 4 * θ₀ := by
  unfold δQS; rw [Real.sqrt_one, one_mul]; exact e3θ_le

theorem δQS_nn : 0 ≤ δQS 1 θ₀ := by
  unfold δQS; rw [Real.sqrt_one, one_mul]; exact expm1_nn 3 (by norm_num)

theorem δCS_le : δCS θ₀ ≤ 7 * θ₀ := by
  unfold δCS
  have he := eθ_le
  have h1 : θ₀ * Real.exp θ₀ ≤ θ₀ * (1 + 2 * θ₀) := mul_le_mul_of_nonneg_left he (by positivity)
  have : 6 * (θ₀ * (1 + 2 * θ₀)) ≤ 7 * θ₀ := by norm_num
  linarith

section
variable (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130)
include h0 h1

theorem cS_two : 1 / 7 ≤ cS 1 ρ ∧ cS 1 ρ ≤ 1 / 6 := by
  unfold cS; rw [Mc_one]
  have h2 : ρ ^ 2 ≤ (1 / 10 ^ 130) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num at h2 ⊢; nlinarith
  · rw [div_le_iff₀ (by norm_num)]; nlinarith

theorem cS_two_pos : 0 < cS 1 ρ := lt_of_lt_of_le (by norm_num) (cS_two ρ h0 h1).1

theorem hS1_two : 24 * (δDS θ₀ ^ 2 + 1 * δQS 1 θ₀ ^ 2) ≤ cS 1 ρ := by
  have hD := pow_le_pow_left₀ δDS_nn δDS_le 2
  have hQ := pow_le_pow_left₀ δQS_nn δQS_le 2
  have hc := (cS_two ρ h0 h1).1
  have : 24 * ((2 * θ₀) ^ 2 + 1 * (4 * θ₀) ^ 2) ≤ 1 / 7 := by norm_num
  nlinarith

theorem hS2_two : 4 * δDS θ₀ ^ 2 ≤ cS 1 ρ := by
  have hD := pow_le_pow_left₀ δDS_nn δDS_le 2
  have hc := (cS_two ρ h0 h1).1
  have : 4 * (2 * θ₀) ^ 2 ≤ 1 / 7 := by norm_num
  nlinarith

/-- the model site at the witness parameters (no `cGS` condition needed) -/
noncomputable def siteTwo : SiteHyp Z0 Z0 Z0 :=
  modelSite (cS 1 ρ) (δDS θ₀) (δQS 1 θ₀) (cS_two_pos ρ h0 h1) δDS_nn δQS_nn (hS1_two ρ h0 h1) (hS2_two ρ h0 h1)

theorem siteTwo_small : SiteSmall (siteTwo ρ h0 h1) where
  hc1 := (cS_two ρ h0 h1).1
  hc2 := (cS_two ρ h0 h1).2
  hD := δDS_le
  hQ := δQS_le
  hm := rfl

theorem epsXf_two_le : epsXf (cS 1 ρ) (δDS θ₀) (δQS 1 θ₀) 1 ≤ 2200 * θ₀ :=
  (siteTwo_small ρ h0 h1).epsX_le

theorem epsXf_two_nn : 0 ≤ epsXf (cS 1 ρ) (δDS θ₀) (δQS 1 θ₀) 1 :=
  (siteTwo ρ h0 h1).epsX_nonneg 1 zero_le_one

theorem bS_two : 1 ≤ bS 2 1 ρ ∧ bS 2 1 ρ ≤ 105000 := by
  unfold bS
  have hs : Real.sqrt 78732 ^ 2 = 78732 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 78732 := Real.sqrt_nonneg _
  have hsl : Real.sqrt 78732 ≤ 281 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  have h12 : Real.sqrt 12 ≤ 4 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  have h120 : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg _
  have ht0 : 0 ≤ 27 * Real.sqrt 12 * ρ := by positivity
  have ht1 : 27 * Real.sqrt 12 * ρ ≤ 108 / 10 ^ 130 := by
    have := mul_le_mul h12 h1 h0 (by norm_num)
    nlinarith
  have hnum : (Real.sqrt 78732 + 27 * Real.sqrt 12 * ρ) ^ 2 ≤ 78732.001 := by
    have e : (Real.sqrt 78732 + 27 * Real.sqrt 12 * ρ) ^ 2
        = Real.sqrt 78732 ^ 2 + 2 * Real.sqrt 78732 * (27 * Real.sqrt 12 * ρ) + (27 * Real.sqrt 12 * ρ) ^ 2 := by ring
    rw [e, hs]
    have a1 : Real.sqrt 78732 * (27 * Real.sqrt 12 * ρ) ≤ 281 * (108 / 10 ^ 130) := mul_le_mul hsl ht1 ht0 (by norm_num)
    have a2 : (27 * Real.sqrt 12 * ρ) ^ 2 ≤ (108 / 10 ^ 130) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
    norm_num at a1 a2 ⊢
    linarith
  have hq : 1 - 324 * ρ ≤ (1 - 162 * ρ) ^ 2 := by nlinarith [sq_nonneg (162 * ρ)]
  have h34 : (1 : ℝ) * (1 - 1 / (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))) = 3 / 4 := by push_cast; norm_num
  rw [h34]
  have hden : (0.74999 : ℝ) ≤ (1 - 162 * ρ) ^ 2 * (3 / 4) := by nlinarith
  have hden0 : 0 < (1 - 162 * ρ) ^ 2 * (3 / 4) := lt_of_lt_of_le (by norm_num) hden
  have hfrac0 : 0 ≤ (Real.sqrt 78732 + 27 * Real.sqrt 12 * ρ) ^ 2 / ((1 - 162 * ρ) ^ 2 * (3 / 4)) :=
    div_nonneg (sq_nonneg _) hden0.le
  have hfrac : (Real.sqrt 78732 + 27 * Real.sqrt 12 * ρ) ^ 2 / ((1 - 162 * ρ) ^ 2 * (3 / 4)) ≤ 104990 := by
    rw [div_le_iff₀ hden0]; nlinarith
  constructor <;> linarith

theorem cGS_two_ge : 4.5e-11 ≤ cGS 2 1 ρ θ₀ := by
  unfold cGS
  rw [qS_one, one_mul]
  obtain ⟨hb1, hb⟩ := bS_two ρ h0 h1
  have hb0 : 0 < bS 2 1 ρ := lt_of_lt_of_le one_pos hb1
  have h2 : 1 / (2 * (105000 : ℝ) ^ 2) ≤ 1 / (2 * bS 2 1 ρ ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have := pow_le_pow_left₀ hb0.le hb 2; linarith
  have he := epsXf_two_le ρ h0 h1
  have he0 := epsXf_two_nn ρ h0 h1
  have h3 : epsXf (cS 1 ρ) (δDS θ₀) (δQS 1 θ₀) 1 ^ 2 ≤ (2200 * θ₀) ^ 2 := pow_le_pow_left₀ he0 he 2
  have h4 : (4.5e-11 : ℝ) + 3 * (2200 * θ₀) ^ 2 ≤ 1 / (2 * (105000 : ℝ) ^ 2) := by norm_num
  linarith

/-- **the k-free conditions of the `G⁻¹` chain hold at the witness parameters** -/
theorem condM0_two : CondM0 2 1 ρ θ₀ where
  hell := le_rfl
  ha := one_pos
  hρ0 := h0
  h216 := by have := pow_le_pow_left₀ h0 h1 2; norm_num at this ⊢; nlinarith
  h162 := by linarith [show (162 : ℝ) * (1 / 10 ^ 130) < 1 by norm_num]
  hθ := by positivity
  hS1 := hS1_two ρ h0 h1
  hS2 := hS2_two ρ h0 h1
  hcG := lt_of_lt_of_le (by norm_num) (cGS_two_ge ρ h0 h1)

theorem κS_le : κS ρ ≤ 816 * ρ := by
  unfold κS
  have hpi := Real.pi_gt_three
  have : ρ / (3 * Real.pi) ≤ ρ := div_le_self h0 (by linarith)
  linarith

theorem νS_le : νS ρ ≤ 816 * ρ := by
  unfold νS
  have hpi := Real.pi_gt_three
  have e1 : ρ / (3 * Real.pi) ≤ ρ := div_le_self h0 (by linarith)
  have hs2 : (1 : ℝ) ≤ 4 * Real.sqrt 2 := by
    have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have e2 : ρ / (3 * Real.pi) / (4 * Real.sqrt 2) ≤ ρ / (3 * Real.pi) := div_le_self (by positivity) hs2
  linarith

theorem δKS_le : δKS ρ θ₀ ≤ 816 * ρ := by
  unfold δKS
  have h := κS_le ρ h0 h1
  have h0' : 0 ≤ κS ρ := by unfold κS; have := Real.pi_pos; positivity
  have he := e2θ_le
  have he0 := expm1_nn 2 (by norm_num)
  have : κS ρ * (Real.exp (2 * θ₀) - 1) ≤ κS ρ * 1 := mul_le_mul_of_nonneg_left (by linarith [show 3 * θ₀ ≤ 1 by norm_num]) h0'
  linarith

theorem δνS_le : δνS ρ θ₀ ≤ 816 * ρ := by
  unfold δνS
  have h := νS_le ρ h0 h1
  have h0' : 0 ≤ νS ρ := by unfold νS; have := Real.pi_pos; positivity
  have he := e2θ_le
  have : νS ρ * (Real.exp (2 * θ₀) - 1) ≤ νS ρ * 1 := mul_le_mul_of_nonneg_left (by linarith [show 3 * θ₀ ≤ 1 by norm_num]) h0'
  linarith

theorem qBS_two : 0 ≤ qBS 2 1 ρ ∧ qBS 2 1 ρ ≤ 1.02 := by
  unfold qBS
  rw [Real.sqrt_one, one_mul]
  exact ⟨(Real.exp_pos _).le, (exp_drift_le ρ h0 h1).trans (by norm_num)⟩

theorem δBS_two : δBS 2 1 ρ θ₀ ≤ 200 * θ₀ := by
  unfold δBS
  rw [Real.sqrt_one, one_mul]
  have he := exp_drift_le ρ h0 h1
  have he0 := (Real.exp_pos (3600 * ((2 : ℕ) : ℝ) * ρ / rr 2)).le
  have h5 := e5θ_le
  have h50 := expm1_nn 5 (by norm_num)
  have hs : Real.sqrt 648 ≤ 25.46 := sqrt_le_of _ _ (by norm_num) (by norm_num)
  have hs0 := Real.sqrt_nonneg 648
  calc Real.exp (3600 * ((2 : ℕ) : ℝ) * ρ / rr 2) * (Real.exp (5 * θ₀) - 1) * Real.sqrt 648
      ≤ 1.0001 * (6 * θ₀) * 25.46 := mul_le_mul (mul_le_mul he h5 h50 (by norm_num)) hs hs0 (by positivity)
    _ ≤ 200 * θ₀ := by norm_num

theorem δS_two : 0 ≤ δS 2 ρ ∧ δS 2 ρ ≤ 2.1e-5 := by
  unfold δS
  have hp := phiC_two_le ρ h0 (h1.trans (by norm_num))
  have hp0 := phiC_two_nn ρ h0
  constructor
  · positivity
  · norm_num at hp ⊢; linarith

theorem bNS_two : bNS 1 ρ (δS 2 ρ) ≤ 1.9e7 := by
  obtain ⟨hd0, hd⟩ := δS_two ρ h0 h1
  obtain ⟨hc1, hc2⟩ := cS_two ρ h0 h1
  have hcp : 0 < cS 1 ρ := lt_of_lt_of_le (by norm_num) hc1
  have hk := κS_le ρ h0 h1
  have hk0 : 0 ≤ κS ρ := by unfold κS; have := Real.pi_pos; positivity
  have hn := νS_le ρ h0 h1
  have hn0 : 0 ≤ νS ρ := by unfold νS; have := Real.pi_pos; positivity
  have hA : A0S 1 (δS 2 ρ) ≤ 1.0001 := by
    unfold A0S; rw [Real.sqrt_one, mul_one, div_le_iff₀ (by linarith)]; nlinarith
  have hA0 : 0 ≤ A0S 1 (δS 2 ρ) := by
    unfold A0S; rw [Real.sqrt_one, mul_one]; exact div_nonneg zero_le_one (by linarith)
  have hcN : cNS 1 ρ (δS 2 ρ) ≤ 3888.4 := by
    unfold cNS
    have : 3888 + 243 * ρ ≤ 3888.0001 := by nlinarith
    have := mul_le_mul this hA hA0 (by norm_num)
    linarith
  have hcN0 : 0 ≤ cNS 1 ρ (δS 2 ρ) := by unfold cNS; positivity
  have hs3 := sqrt3_le'
  have hs30 := Real.sqrt_nonneg 3
  have hdN : dNS 1 ρ (δS 2 ρ) ≤ 1944.2 := by
    unfold dNS
    have : 1944 + 81 * Real.sqrt 3 / 2 * ρ ≤ 1944.0001 := by nlinarith
    have := mul_le_mul this hA hA0 (by norm_num)
    linarith
  have hdN0 : 0 ≤ dNS 1 ρ (δS 2 ρ) := by unfold dNS; positivity
  have hgN : gNS 1 (δS 2 ρ) ≤ 20.26 := by
    unfold gNS; have := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 81 / 4); linarith
  have hgN0 : 0 ≤ gNS 1 (δS 2 ρ) := by unfold gNS; positivity
  have hdc : dNS 1 ρ (δS 2 ρ) / cS 1 ρ ≤ 1944.2 * 7 := by
    rw [div_le_iff₀ hcp]; nlinarith
  have hdc0 : 0 ≤ dNS 1 ρ (δS 2 ρ) / cS 1 ρ := div_nonneg hdN0 hcp.le
  have hsc : (0.377 : ℝ) ≤ Real.sqrt (cS 1 ρ) := by
    rw [show (0.377 : ℝ) = Real.sqrt (0.377 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hds : dNS 1 ρ (δS 2 ρ) / Real.sqrt (cS 1 ρ) ≤ 5200 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hsc)]; nlinarith
  have hds0 : 0 ≤ dNS 1 ρ (δS 2 ρ) / Real.sqrt (cS 1 ρ) := div_nonneg hdN0 (Real.sqrt_nonneg _)
  have t1 : κS ρ * (dNS 1 ρ (δS 2 ρ) / cS 1 ρ) ≤ (816 / 10 ^ 130) * (1944.2 * 7) :=
    mul_le_mul (hk.trans (by nlinarith)) hdc hdc0 (by positivity)
  have t10 : 0 ≤ κS ρ * (dNS 1 ρ (δS 2 ρ) / cS 1 ρ) := mul_nonneg hk0 hdc0
  have t2 : (cNS 1 ρ (δS 2 ρ) + κS ρ * (dNS 1 ρ (δS 2 ρ) / cS 1 ρ)) ^ 2
      ≤ (3888.4 + (816 / 10 ^ 130) * (1944.2 * 7)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (add_le_add hcN t1) 2
  have t3 : (gNS 1 (δS 2 ρ) + dNS 1 ρ (δS 2 ρ) / Real.sqrt (cS 1 ρ)) ^ 2 ≤ (20.26 + 5200) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (add_le_add hgN hds) 2
  have t4 : νS ρ * (gNS 1 (δS 2 ρ) + dNS 1 ρ (δS 2 ρ) / Real.sqrt (cS 1 ρ)) ^ 2
      ≤ (816 / 10 ^ 130) * (20.26 + 5200) ^ 2 :=
    mul_le_mul (hn.trans (by nlinarith)) t3 (sq_nonneg _) (by positivity)
  have t5 : dNS 1 ρ (δS 2 ρ) ^ 2 ≤ 1944.2 ^ 2 := pow_le_pow_left₀ hdN0 hdN 2
  unfold bNS
  have hfin : (3888.4 + (816 / 10 ^ 130) * (1944.2 * 7)) ^ 2 + (816 / 10 ^ 130) * (20.26 + 5200) ^ 2
      + 1944.2 ^ 2 + 1 ≤ (1.9e7 : ℝ) := by norm_num
  linarith

theorem bNS_two_pos : 0 < bNS 1 ρ (δS 2 ρ) := bNS_pos 1 ρ (δS 2 ρ) (condM0_two ρ h0 h1).νS_nonneg

/-- **the model `G⁻¹` structure of the witness parameters is in the DL86 small regime** -/
theorem ginvSmall_two : GinvSmall (condM0_two ρ h0 h1).ginv where
  gam :=
    { site := siteTwo_small ρ h0 h1
      hq := qS_one
      hcG := cGS_two_ge ρ h0 h1 }
  hδC := δCS_le
  hκ := (κS_le ρ h0 h1).trans (by nlinarith)
  hδK := (δKS_le ρ h0 h1).trans (by nlinarith)
  hν := (νS_le ρ h0 h1).trans (by nlinarith)
  hδν := (δνS_le ρ h0 h1).trans (by nlinarith)
  hδB := δBS_two ρ h0 h1
  hM := rfl

theorem EGM0_two_le : EGM0 2 1 ρ θ₀ (condM0_two ρ h0 h1) ≤ 1 / 10 ^ 36 := (ginvSmall_two ρ h0 h1).EG_le

theorem EGM0_two_nn : 0 ≤ EGM0 2 1 ρ θ₀ (condM0_two ρ h0 h1) := (ginvSmall_two ρ h0 h1).EG_nonneg

theorem KhatM0_two (hρ : ρ ≤ 1 / 10 ^ 130) : 0 < KhatM0 2 1 1 ρ ∧ KhatM0 2 1 1 ρ ≤ 4001 :=
  ⟨AdalyFormal.M0Finish.KhatM0_pos' ρ h0 (hρ.trans (by norm_num)),
    AdalyFormal.M0Finish.KhatM0_le ρ h0 (hρ.trans (by norm_num))⟩

theorem invK_two : (2.4e-4 : ℝ) ≤ 1 / KhatM0 2 1 1 ρ := by
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have := one_div_le_one_div_of_le hK hKl
  have h2 : (2.4e-4 : ℝ) ≤ 1 / 4001 := by norm_num
  linarith

theorem hEG_two : 4 * EGM0 2 1 ρ θ₀ (condM0_two ρ h0 h1) ≤ 1 / KhatM0 2 1 1 ρ := by
  have := EGM0_two_le ρ h0 h1
  have := invK_two ρ h0 h1
  have : 4 * (1 / 10 ^ 36 : ℝ) ≤ 2.4e-4 := by norm_num
  linarith

/-- **the model Schur structure of `ENfree` is in the DL86 small regime** -/
theorem nSmall_two (hK : 0 < KhatM0 2 1 1 ρ) (hEG : 4 * EGM0 2 1 ρ θ₀ (condM0_two ρ h0 h1) ≤ 1 / KhatM0 2 1 1 ρ) :
    NSmall ((condM0_two ρ h0 h1).modelN (1 / KhatM0 2 1 1 ρ) (qBS 2 1 ρ) (bNS 1 ρ (δS 2 ρ)) (by positivity) hEG
      (qBS_two ρ h0 h1).1 (bNS_two_pos ρ h0 h1)) where
  ginv := ginvSmall_two ρ h0 h1
  hcg := invK_two ρ h0 h1
  hqb := (qBS_two ρ h0 h1).2
  hbN := (bNS_two ρ h0 h1).trans (by norm_num)

theorem ENfree_two (hK : 0 < KhatM0 2 1 1 ρ) (hEG : 4 * EGM0 2 1 ρ θ₀ (condM0_two ρ h0 h1) ≤ 1 / KhatM0 2 1 1 ρ) :
    ENfree 2 1 1 ρ θ₀ (condM0_two ρ h0 h1) hK hEG ≤ 1 / 10 ^ 12 ∧
    ENfree 2 1 1 ρ θ₀ (condM0_two ρ h0 h1) hK hEG < 1 / bNS 1 ρ (δS 2 ρ) :=
  ⟨(nSmall_two ρ h0 h1 hK hEG).EN_le, (nSmall_two ρ h0 h1 hK hEG).EN_lt⟩

end

#print axioms exp_le_quad
#print axioms condM0_two
#print axioms ginvSmall_two
#print axioms bNS_two
#print axioms ENfree_two

end AdalyFormal.DLayer
