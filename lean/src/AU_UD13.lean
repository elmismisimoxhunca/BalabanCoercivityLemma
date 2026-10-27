import UD13

/-! AU_UD13 -- c-free numerics for the unit-floor hypotheses: `6 Mc + 4 ell + 165 <= 4 M` (as UD13) and `6 Mc + 4 ell + 25 <= R M` for `R >= 22`, `m >= 8`, `M = ell^m = ell Mc`. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.M2UnitCharts

theorem headline_numericsU {ell m R : ℕ} (hell : 2 ≤ ell) (hm : 8 ≤ m) (hR : 22 ≤ R) :
    ell ^ m = ell * ell ^ (m - 1) ∧ 0 < ell ^ (m - 1) ∧
    6 * ell ^ (m - 1) + 4 * ell + 165 ≤ 4 * ell ^ m ∧
    6 * ell ^ (m - 1) + 4 * ell + 25 ≤ R * ell ^ m := by
  have hpow : ell ^ m = ell * ell ^ (m - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have h7 : ell ^ 7 ≤ ell ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 2 ^ 6 ≤ ell ^ 6 := Nat.pow_le_pow_left hell 6
  have h7' : ell ^ 7 = ell * ell ^ 6 := by ring
  have hbig : 64 * ell ≤ ell ^ (m - 1) := by
    have : ell * 64 ≤ ell * ell ^ 6 := Nat.mul_le_mul_left _ (by norm_num at h6 ⊢; omega)
    nlinarith
  refine ⟨hpow, by nlinarith, ?_, ?_⟩
  · rw [hpow]
    nlinarith
  · have h2 : 2 * ell + 12 ≤ ell ^ m := by
      rw [hpow]; nlinarith
    have h3 : 22 * ell ^ m ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR
    have h4 : 6 * ell ^ (m - 1) + 4 * ell + 25 ≤ 22 * ell ^ m := by
      rw [hpow]; nlinarith
    omega

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.headline_numericsU
