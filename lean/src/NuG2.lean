import NuG1
import NtCvOF11
import NtCvOI5
import NtCvOF12
import NtCvOU3

/-!
# NuG2 -- row data of the Z-block (lane ncwdh_ell2_20261018)

* `zrow_rows_zero`: `zrow ρ = 0` forces `ρ j r = 0` on all row starts.
* `rowsum_eq_fSum`: the sum of a chain vector over chain row `i` is `fSum ell j (fe e)` at the row start, for the level `j` of the row.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.SuTwoInner (hsInner)

section
variable [CfData]
variable {ell M R : ℕ}

theorem dgS_eq_zero {a : ℝ} (h : dgS a = 0) : a = 0 := by
  have h1 : hsInner (dgS a) (dgS 1) = 0 := by rw [h]; exact hsInner_zero_left' _
  rw [hsInner_dgS_dgS] at h1
  have hc := c0_pos
  have : a * 1 * c0 = 0 := h1
  rcases mul_eq_zero.mp this with h2 | h2
  · simpa using h2
  · exact absurd h2 hc.ne'


/-- a zero Z-row field has zero profile on all row starts. -/
theorem zrow_rows_zero (hg : NGeo ell M R) (hM : 0 < M) (hR : 1 ≤ R) (ρ : ℕ → ℕ → ℝ)
    (h : zrow (geomOf ell 2 (neS ell M R)) ρ = 0) :
    ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → ρ j r = 0 := by
  intro j hj r hr
  have hell : 0 < ell := by have := hg.hell; omega
  have hrI : neP0 ell M R ≤ r ∧ r < neQ0 ell M R := hrowJ_nested hg hj r (by
    have := (isRowN_dvd hr).1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simpa using hr
    · simp only [pow_one] at this ⊢
      rw [Nat.mul_div_cancel' this]; exact hr
    · rw [Nat.mul_div_cancel' this]; exact hr)
  have hN : neQ0 ell M R + 1 ≤ neN ell M R := ne_Q0_lt_N_two hg.hell hM hR
  have hdim : ∀ μ : Fin 3, scaleUp ell 2 (neLu M R) μ + 1 = neN ell M R := fun μ => ne_scaleUp hell hM μ
  let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := fun μ => ⟨if μ = 0 then r else 0, by
    have := hdim μ
    split_ifs <;> omega⟩
  have hy0 : (y 0).val = r := by simp [y]
  have hcrs : Crs (ell ^ j) y := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [hy0]; exact (isRowN_dvd hr).1
    · simp [y, hμ]
  have hmem : (y, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) j :=
    (bondsLam_one_iff hg hM hj y).mpr ⟨hcrs, by rw [hy0]; exact hr⟩
  let p : BIdx (geomOf ell 2 (neS ell M R)) := ⟨⟨j, by simp [geomOf]; omega⟩, ⟨(y, 1), hmem⟩⟩
  have hp := congrArg (fun z : FSp (geomOf ell 2 (neS ell M R)) => z p) h
  simp only at hp
  have hval : (zrow (geomOf ell 2 (neS ell M R)) ρ) p = dgS (ρ j r) := by
    show (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = _
    simp [p, hy0]
  rw [hval] at hp
  exact dgS_eq_zero hp

end

end AdalyFormal.NcwdhTwo
