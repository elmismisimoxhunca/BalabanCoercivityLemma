import ASC6

/-!
# ASW1 -- numeric: `ThetaM0 2 1 1 ρ < 1/1000` for every `0 ≤ ρ ≤ 3·10⁻¹¹`  (ell = 2, a = 1, t = 1).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.AsmM0

open AdalyFormal.BondComposite (rr rr_nonneg rr_sq)

theorem sqrt3_le : Real.sqrt 3 ≤ 1.7321 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
theorem sqrt3_nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
theorem sqrt6_le : Real.sqrt 6 ≤ 2.45 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
theorem sqrt2_ge : 1.4 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)

theorem Mc_one : Mc 1 = 6 := by
  unfold Mc; norm_num

theorem Stil_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 3e-11) :
    Stil (Real.sqrt 3) (Real.sqrt (Mc 1)) ρ ≤ 9e8 * ρ := by
  rw [Mc_one]
  have hR := sqrt3_le; have hR0 := sqrt3_nn; have hC := sqrt6_le
  have hC0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hC2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hden : 0 < 1 - 162 * ρ := by nlinarith
  have hW : Wc (Real.sqrt 3) ρ ≤ 281 := by
    unfold Wc; rw [div_le_iff₀ hden]; nlinarith
  have hW0 : 0 ≤ Wc (Real.sqrt 3) ρ := by unfold Wc; positivity
  have hX : 324 * Real.sqrt 3 * ρ * (3 + ρ) / (1 - 162 * ρ) ≤ 1690 * ρ := by
    rw [div_le_iff₀ hden]; nlinarith [mul_nonneg hR0 h0, mul_nonneg h0 h0]
  have hX0 : 0 ≤ 324 * Real.sqrt 3 * ρ * (3 + ρ) / (1 - 162 * ρ) := by positivity
  have hV : Vc (Real.sqrt 3) (Real.sqrt 6) ρ ≤ 3e6 * ρ := by
    unfold Vc
    rw [hC2]
    have h1' : 2 * Real.sqrt 3 * ρ + 324 * Real.sqrt 3 * ρ * (3 + ρ) / (1 - 162 * ρ) ≤ 1700 * ρ := by
      nlinarith [mul_nonneg hR0 h0]
    have h2' : 0 ≤ 2 * Real.sqrt 3 * ρ + 324 * Real.sqrt 3 * ρ * (3 + ρ) / (1 - 162 * ρ) := by positivity
    calc Wc (Real.sqrt 3) ρ * 6 * (2 * Real.sqrt 3 * ρ + 324 * Real.sqrt 3 * ρ * (3 + ρ) / (1 - 162 * ρ))
        ≤ 281 * 6 * (1700 * ρ) := by
          apply mul_le_mul (by nlinarith) h1' h2' (by norm_num)
      _ ≤ 3e6 * ρ := by nlinarith
  have hV0 : 0 ≤ Vc (Real.sqrt 3) (Real.sqrt 6) ρ := by unfold Vc Wc; positivity
  unfold Stil
  have hin : 2 * Real.sqrt 3 * ρ * Real.sqrt 6 + Vc (Real.sqrt 3) (Real.sqrt 6) ρ ≤ 3.1e6 * ρ := by
    nlinarith [mul_nonneg hR0 h0, mul_nonneg (mul_nonneg hR0 h0) hC0]
  have hin0 : 0 ≤ 2 * Real.sqrt 3 * ρ * Real.sqrt 6 + Vc (Real.sqrt 3) (Real.sqrt 6) ρ := by positivity
  calc Wc (Real.sqrt 3) ρ * (2 * Real.sqrt 3 * ρ * Real.sqrt 6 + Vc (Real.sqrt 3) (Real.sqrt 6) ρ) + 2 * Real.sqrt 3 * ρ
      ≤ 281 * (3.1e6 * ρ) + 2 * Real.sqrt 3 * ρ := by
        have := mul_le_mul hW hin hin0 (by norm_num); linarith
    _ ≤ 9e8 * ρ := by nlinarith

theorem Stil_nn (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 3e-11) : 0 ≤ Stil (Real.sqrt 3) (Real.sqrt (Mc 1)) ρ := by
  rw [Mc_one]; unfold Stil Vc Wc
  have hden : 0 < 1 - 162 * ρ := by nlinarith
  positivity

theorem phiC_two_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 3e-11) : phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ≤ 1e-6 := by
  unfold phiC
  have hrr : 0.7 ≤ rr 2 := by
    unfold rr; apply Real.le_sqrt_of_sq_le; push_cast; norm_num
  have hrr0 : 0 < rr 2 := by linarith
  have hs : 3600 * ((2 : ℕ) : ℝ) * ρ ≤ 2.2e-7 := by push_cast; nlinarith
  have hx : 3600 * ((2 : ℕ) : ℝ) * ρ / rr 2 ≤ 3.2e-7 := by
    rw [div_le_iff₀ hrr0]; nlinarith
  have hx0 : 0 ≤ 3600 * ((2 : ℕ) : ℝ) * ρ / rr 2 := by positivity
  have hexp : Real.exp (3600 * ((2 : ℕ) : ℝ) * ρ / rr 2) ≤ 3 := by
    calc _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  calc _ ≤ 3.2e-7 * 3 := mul_le_mul hx hexp (Real.exp_pos _).le (by norm_num)
    _ ≤ 1e-6 := by norm_num

theorem phiC_two_nn (ρ : ℝ) (h0 : 0 ≤ ρ) : 0 ≤ phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) := by
  unfold phiC
  have : 0 ≤ rr 2 := rr_nonneg 2
  positivity

theorem Theta_num (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 3e-11) : ThetaM0 2 1 1 ρ < min (1 : ℝ) 1 / 1000 := by
  have hS := Stil_le ρ h0 h1
  have hS0 := Stil_nn ρ h0 h1
  have hS2 : Stil (Real.sqrt 3) (Real.sqrt (Mc 1)) ρ ^ 2 ≤ 7.3e-4 := by
    have : Stil (Real.sqrt 3) (Real.sqrt (Mc 1)) ρ ≤ 2.7e-2 := by nlinarith
    nlinarith
  have hphi := phiC_two_le ρ h0 h1
  have hphi0 := phiC_two_nn ρ h0
  have hphi2 : phiC 2 (3600 * ((2 : ℕ) : ℝ) * ρ) ^ 2 ≤ 1e-12 := by
    calc _ ≤ (1e-6 : ℝ) ^ 2 := pow_le_pow_left₀ hphi0 hphi 2
      _ = 1e-12 := by norm_num
  have hpi := Real.pi_gt_three
  have h2 := sqrt2_ge
  have hq : 272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2) ≤ 6 * ρ := by
    have e1 : ρ / (3 * Real.pi) ≤ ρ / 9 := div_le_div_of_nonneg_left h0 (by norm_num) (by linarith)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1.4)]
  unfold ThetaM0
  have e1 : min (1 : ℝ) 1 / 1000 = 1 / 1000 := by norm_num
  rw [e1]
  norm_num
  nlinarith

#print axioms Stil_le
#print axioms phiC_two_le
#print axioms Theta_num

end AdalyFormal.AsmM0
