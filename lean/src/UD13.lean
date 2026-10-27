import UD12

/-!
# UD13 -- the numeric hypotheses of `unit_floor_class` are met by the headline's quantifier structure (lane m2_unitcharts_20261014)

The headline `P428Target8` is `∀ ell ≥ 2, ∀ a > 0, ∃ m₀ (prover), ∀ m ≥ m₀ (M = ell^m), ∃ R₀ (prover), ∀ R ≥ R₀, ...`.
`headline_numerics`: for `ell ≥ 2`, `m ≥ 8`, `R ≥ 22`, `M = ell^m`, `Mc = ell^(m-1)`:  `M = ell * Mc`, `0 < Mc`, `6 Mc + 4 ell + 165 ≤ 5 M` and `21 M + 2 ell + 12 ≤ R M`
(the hypotheses `hMc`, `hMc0`, `hMbig`, `hRM` of `unit_floor_class`); so `m₀ = 8`, `R₀ = 22` suffice.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.M2UnitCharts

theorem headline_numerics {ell m R : ℕ} (hell : 2 ≤ ell) (hm : 8 ≤ m) (hR : 22 ≤ R) :
    ell ^ m = ell * ell ^ (m - 1) ∧ 0 < ell ^ (m - 1) ∧
    6 * ell ^ (m - 1) + 4 * ell + 165 ≤ 5 * ell ^ m ∧
    21 * ell ^ m + 2 * ell + 12 ≤ R * ell ^ m := by
  have hpow : ell ^ m = ell * ell ^ (m - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have h7 : ell ^ 7 ≤ ell ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 2 ^ 6 ≤ ell ^ 6 := Nat.pow_le_pow_left hell 6
  have h7' : ell ^ 7 = ell * ell ^ 6 := by ring
  have hbig : ell + 42 ≤ ell ^ (m - 1) := by
    have : ell * 64 ≤ ell * ell ^ 6 := Nat.mul_le_mul_left _ (by norm_num at h6 ⊢; omega)
    nlinarith
  refine ⟨hpow, by omega, ?_, ?_⟩
  · rw [hpow]
    nlinarith
  · have h2 : 2 * ell + 12 ≤ ell ^ m := by
      rw [hpow]; nlinarith
    nlinarith

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.headline_numerics
