import UD13
import AC_Base

/-!
# AC_UD13 -- numerics for the generalised unit-floor hypotheses (lane allc_20261016)

UD13 `headline_numerics` (m >= 8, R >= 22): `6 Mc + 4 ell + 165 <= 5 M` and `21 M + 2 ell + 12 <= R M`.  The class cube of factor `fc` needs the room `4 M n` (instead of `5 M n`)
in `class_cube_atAC` and the margin `3 fc M` (instead of `21 M`): `6 Mc + 4 ell + 165 <= 4 M` (still `m >= 8`) and `3 (fc M) + 2 ell + 12 <= R M` for `R >= 3 fc + 22`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.M2UnitCharts

theorem headline_numericsAC {ell m R fc : ℕ} (hell : 2 ≤ ell) (hm : 8 ≤ m) (hR : 3 * fc + 22 ≤ R) :
    ell ^ m = ell * ell ^ (m - 1) ∧ 0 < ell ^ (m - 1) ∧
    6 * ell ^ (m - 1) + 4 * ell + 165 ≤ 4 * ell ^ m ∧
    3 * (fc * ell ^ m) + 2 * ell + 12 ≤ R * ell ^ m := by
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
    have h3 : (3 * fc + 22) * ell ^ m ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR
    nlinarith

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.headline_numericsAC
