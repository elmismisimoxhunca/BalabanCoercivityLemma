import DLR101

/-!
# DL102 -- the extra smallness of DL101 (`eps2op·K̂ < 1`) holds in the explicit window of DL88 (ℓ = 2, a = t = 1, θ₀ = 10⁻⁴⁵)

`eps2op_two` : for `0 ≤ ρ ≤ 10⁻¹³⁰`, `0 ≤ β ≤ 10⁻²⁵⁰` and any `Num : M0ClassNum 2 1 1 ρ β θ₀`:
`0 ≤ eps2op Num ≤ 10⁻¹³³` and `eps2op Num · K̂ < 1`  (nW ≤ 4·10¹², CHfree ≤ 10⁷⁹, JSfree β ≤ β, K2free ≤ 5·10¹¹).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1000

namespace AdalyFormal.DLayer

open AdalyFormal.AsmM0 (KhatM0)

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

theorem eps2op_two (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)
    (Num : M0ClassNum 2 1 1 ρ β θ₀) :
    0 ≤ eps2op Num ∧ eps2op Num ≤ 1 / 10 ^ 133 ∧ eps2op Num * KhatM0 2 1 1 ρ < 1 := by
  have hW : GLv.nW 2 1 ρ θ₀ ≤ 4e12 := (ginvSmall_two ρ h0 h1).nW_le
  have hW0 : 0 ≤ GLv.nW 2 1 ρ θ₀ := (ginvSmall_two ρ h0 h1).nW_nonneg'
  obtain ⟨hC0, hC⟩ := CHfree_two ρ h0 h1 Num.hK Num.hc Num.hEG
  obtain ⟨hK20, hK2⟩ := K2free_two ρ h0 h1
  have hJ := JSfree_le β hβ0 (hβ1.trans (by norm_num))
  have hJ0 := JSfree_nonneg β hβ0
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have hW2 : GLv.nW 2 1 ρ θ₀ ^ 2 ≤ (4e12) ^ 2 := pow_le_pow_left₀ hW0 hW 2
  have hle : eps2op Num ≤ 2 * (4e12) ^ 2 * 1e79 * (1 / 10 ^ 250) * 5e11 := by
    unfold eps2op
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by norm_num)) hC hC0 (by positivity))
      (hJ.trans hβ1) hJ0 (by positivity)) hK2 hK20 (by positivity)
  have hnum : 2 * (4e12 : ℝ) ^ 2 * 1e79 * (1 / 10 ^ 250) * 5e11 ≤ 1 / 10 ^ 133 := by
    have e : (2 : ℝ) * (4e12 : ℝ) ^ 2 * 1e79 * (1 / 10 ^ 250) * 5e11 = 16 / 10 ^ 135 := by norm_num
    rw [e]; norm_num
  have h0' := eps2op_nonneg Num
  refine ⟨h0', hle.trans hnum, ?_⟩
  have := mul_le_mul (hle.trans hnum) hKl hK.le (by positivity)
  have : (1 / 10 ^ 133 : ℝ) * 4001 < 1 := by norm_num
  linarith

/-- the numeral of the slope bound (kernel-evaluated): `2·(4·10¹²)²·10⁷⁹·5·10¹¹ = 1.6·10¹¹⁶` -/
theorem eps2op_two_coef : (2 : ℝ) * (4e12) ^ 2 * 1e79 * 5e11 = 16e115 := by norm_num

/-- **slope form** (added 2026-10-13 for the coordinator's question, REPORT entry 53): on the same numerics, `eps2op` is at most
`1.6·10¹¹⁶·β` and `eps2op·K̂` at most `1.6·10¹¹⁶·4001·β`, for every `β ≤ 10⁻²⁵⁰` at which a package exists
(`m0ClassNum_two` provides one for every such `β`). -/
theorem eps2op_two_slope (ρ β : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 10 ^ 250)
    (Num : M0ClassNum 2 1 1 ρ β θ₀) :
    eps2op Num ≤ 16e115 * β ∧ eps2op Num * KhatM0 2 1 1 ρ ≤ 16e115 * 4001 * β := by
  have hW : GLv.nW 2 1 ρ θ₀ ≤ 4e12 := (ginvSmall_two ρ h0 h1).nW_le
  have hW0 : 0 ≤ GLv.nW 2 1 ρ θ₀ := (ginvSmall_two ρ h0 h1).nW_nonneg'
  obtain ⟨hC0, hC⟩ := CHfree_two ρ h0 h1 Num.hK Num.hc Num.hEG
  obtain ⟨hK20, hK2⟩ := K2free_two ρ h0 h1
  have hJ := JSfree_le β hβ0 (hβ1.trans (by norm_num))
  have hJ0 := JSfree_nonneg β hβ0
  obtain ⟨hK, hKl⟩ := KhatM0_two ρ h0 h1 h1
  have hW2 : GLv.nW 2 1 ρ θ₀ ^ 2 ≤ (4e12) ^ 2 := pow_le_pow_left₀ hW0 hW 2
  have hle : eps2op Num ≤ 2 * (4e12) ^ 2 * 1e79 * β * 5e11 := by
    unfold eps2op
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by norm_num)) hC hC0 (by positivity))
      hJ hJ0 (by positivity)) hK2 hK20 (by positivity)
  have hslope : eps2op Num ≤ 16e115 * β := by
    calc eps2op Num ≤ 2 * (4e12) ^ 2 * 1e79 * β * 5e11 := hle
      _ = ((2 : ℝ) * (4e12) ^ 2 * 1e79 * 5e11) * β := by ring
      _ = 16e115 * β := by rw [eps2op_two_coef]
  have h0' := eps2op_nonneg Num
  refine ⟨hslope, ?_⟩
  calc eps2op Num * KhatM0 2 1 1 ρ ≤ (16e115 * β) * 4001 := mul_le_mul hslope hKl hK.le (by positivity)
    _ = 16e115 * 4001 * β := by ring

#print axioms eps2op_two
#print axioms eps2op_two_coef
#print axioms eps2op_two_slope

end AdalyFormal.DLayer
