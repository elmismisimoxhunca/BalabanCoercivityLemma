import CG6a

/-!
# CG6b -- the box of `7ℓ` cells: distance, collar and cube index
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.UnifLane.Z (cellZ wo div_eq_iff')

variable {L : PeriodicLatticeExtent}

theorem cell_abs {S : ℕ} (hS : 0 < S) (o : Z3) (n : ℕ) {p : Z3}
    (hp : ∀ μ, o μ / (S : ℤ) - n ≤ cellZ (S : ℤ) o p μ ∧ cellZ (S : ℤ) o p μ ≤ o μ / (S : ℤ) + n) (μ : Fin 3) :
    (p μ).natAbs ≤ S * (n + 1) := by
  have hSI : (0 : ℤ) < S := by exact_mod_cast hS
  obtain ⟨h1, h2⟩ := hp μ
  set C := cellZ (S : ℤ) o p μ with hC
  have hCd : (p μ + o μ) / (S : ℤ) = C := rfl
  obtain ⟨c1, c2⟩ := (div_eq_iff' hSI).mp hCd
  have e1 : (o μ / (S : ℤ) - n) * S ≤ C * S := mul_le_mul_of_nonneg_right h1 hSI.le
  have e2 : C * S ≤ (o μ / (S : ℤ) + n) * S := mul_le_mul_of_nonneg_right h2 hSI.le
  have e3 : (o μ / (S : ℤ) - n) * S = (o μ / (S : ℤ)) * S - n * S := by ring
  have e4 : (o μ / (S : ℤ) + n) * S = (o μ / (S : ℤ)) * S + n * S := by ring
  have e5 : (o μ / (S : ℤ)) * S + o μ % (S : ℤ) = o μ := by
    have := Int.mul_ediv_add_emod (o μ) (S : ℤ); linarith
  have e6 : 0 ≤ o μ % (S : ℤ) := Int.emod_nonneg _ hSI.ne'
  have e7 : o μ % (S : ℤ) < S := Int.emod_lt_of_pos _ hSI
  have e8 : ((S * (n + 1) : ℕ) : ℤ) = (n : ℤ) * S + S := by push_cast; ring
  have : (p μ).natAbs ≤ S * (n + 1) := by
    zify
    rw [abs_le]
    constructor <;> nlinarith
  exact this

theorem box_arith (ell S B2 R L1 : ℕ) (hS : S = ell * B2) (hell : 2 ≤ ell) (hR : 24 * ell + 25 ≤ R) (hL1 : L1 = ell * S) :
    (21 * ell + 3) * S + 3 * L1 + 3 * (12 * B2) < R * S + 1 := by
  subst hL1
  have h1 : (24 * ell + 25) * S ≤ R * S := Nat.mul_le_mul_right _ hR
  have h2 : 2 * B2 ≤ S := by rw [hS]; nlinarith [Nat.zero_le B2]
  nlinarith

end AdalyFormal.CoverGeom
