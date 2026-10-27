import CvOI4

/-!
# CvOI5 -- a saddle of the chain form gives the genuine slice equation `ginvProf f = Wt rho_v` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

/-- row slices lie in `[P0,Q0)`. -/
theorem hrowJ_nested (hg : NGeo ell M R) {j : ℕ} (hj : j ≤ 2) (v : ℕ) (h : isRowN ell M R j (ell ^ j * (v / ell ^ j))) :
    neP0 ell M R ≤ v ∧ v < neQ0 ell M R := by
  have hell := hg.hell
  have hpos : 0 < ell ^ j := pow_pos (by omega) j
  have hst : isStart ell M R (ell ^ j * (v / ell ^ j)) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact isStart_0 h
    · exact isStart_1 h
    · exact isStart_2 h
  obtain ⟨t1, -, -, -⟩ := tile_step hg hst
  rw [rowLen_of_isRowN hg h] at t1
  have h1 := Nat.mul_div_le v (ell ^ j)
  have h2 : v < ell ^ j * (v / ell ^ j) + ell ^ j := by
    have := Nat.lt_mul_div_succ v hpos; rw [mul_add, mul_one] at this; exact this
  refine ⟨?_, by omega⟩
  -- start is at least P0
  have hd := (isRowN_dvd h).1
  have : neP0 ell M R ≤ ell ^ j * (v / ell ^ j) := by
    have := hg.hP0P1; have := hg.hP1A; have := hg.hAB'; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simp only [isRowN, reg0] at h; omega
    · simp only [isRowN, reg1] at h; omega
    · simp only [isRowN, reg2] at h; omega
  omega

theorem levN_le (v : ℕ) : levN ell M R v ≤ 2 := by
  unfold levN; split_ifs <;> omega

/-- `Wt` at a slice of `[P0,Q0)` sees exactly one row. -/
theorem Wt_single (hg : NGeo ell M R) {v : ℕ} (hv : neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (ρ : ℕ → ℕ → ℝ) :
    Wt ell (isRowN ell M R) ρ v =
      (((ell : ℝ) ^ levN ell M R v)⁻¹) * ((((ell : ℝ) ^ 2)⁻¹) ^ levN ell M R v) * ρ (levN ell M R v) (rstartN ell M R v) := by
  classical
  unfold Wt
  have hterm : ∀ j ∈ Finset.range 3, (((ell : ℝ) ^ j)⁻¹) * ((((ell : ℝ) ^ 2)⁻¹) ^ j) *
      (if isRowN ell M R j (ell ^ j * (v / ell ^ j)) then ρ j (ell ^ j * (v / ell ^ j)) else 0) =
      if j = levN ell M R v then (((ell : ℝ) ^ j)⁻¹) * ((((ell : ℝ) ^ 2)⁻¹) ^ j) * ρ j (ell ^ j * (v / ell ^ j)) else 0 := by
    intro j hj
    have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
    by_cases h : j = levN ell M R v
    · rw [if_pos ((row_unique hg hv hj2).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((row_unique hg hv hj2).mp h')), if_neg h]; ring
  rw [Finset.sum_congr rfl hterm]
  have hl := levN_le (ell := ell) (M := M) (R := R) v
  unfold rstartN
  rcases (show levN ell M R v = 0 ∨ levN ell M R v = 1 ∨ levN ell M R v = 2 by omega) with h | h | h <;>
    simp [Finset.sum_range_succ, h]

end AdalyFormal.CoverOmega
