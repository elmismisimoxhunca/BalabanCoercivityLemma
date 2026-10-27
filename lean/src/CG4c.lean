import CG4b

/-!
# CG4c -- ball coordinates versus torus cells
`iota_cell`: a cell of ball coordinates (side `s`, offset the torus coordinates of the centre) lands in ONE torus `s`-cell
(index `c mod n`, `n = (L+1)/s`), cyclically.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift iota_shift2)
open AdalyFormal.UnifLane.Z (cellZ wo)

variable {L : PeriodicLatticeExtent}

theorem int_mod_cell {s n c r : ℤ} (hs : 0 < s) (hn : 0 < n) (hr0 : 0 ≤ r) (hr : r < s) :
    (s * c + r) % (s * n) = s * (c % n) + r := by
  have h1 := Int.emod_add_mul_ediv c n
  have h2 : s * c + r = (s * (c % n) + r) + (s * n) * (c / n) := by
    calc s * c + r = s * (c % n + n * (c / n)) + r := by rw [h1]
      _ = _ := by ring
  rw [h2, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · have := Int.emod_nonneg c hn.ne'
    positivity
  · have h3 : c % n < n := Int.emod_lt_of_pos c hn
    nlinarith

theorem int_cell_div {s n c r : ℤ} (hs : 0 < s) (hr0 : 0 ≤ r) (hr : r < s) : (s * c + r) / s = c := by
  rw [add_comm, Int.add_mul_ediv_left _ _ hs.ne', Int.ediv_eq_zero_of_lt hr0 hr]; simp

/-- the torus `s`-cell of the image of a ball-coordinate point depends only on its cell. -/
theorem iota_cell (w : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) (μ : Fin 3) (hN : s ∣ L μ + 1) (p : Z3) :
    (((iota w p μ).val / s : ℕ) : ℤ) = cellZ (s : ℤ) (wo w) p μ % (((L μ + 1) / s : ℕ) : ℤ) := by
  obtain ⟨n, hn⟩ := hN
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hn; omega
    · exact h
  have hsI : (0 : ℤ) < s := by exact_mod_cast hs
  have hnI : (0 : ℤ) < n := by exact_mod_cast hn0
  have hLn : (L μ + 1) / s = n := by rw [hn]; exact Nat.mul_div_cancel_left _ hs
  rw [hLn]
  have hv := AdalyFormal.M2GlueGeo.iota_val_int w p μ
  have hNI : (((L μ + 1 : ℕ)) : ℤ) = (s : ℤ) * n := by rw [hn]; push_cast; ring
  set a : ℤ := (p μ) + wo w μ with ha
  have hc : cellZ (s : ℤ) (wo w) p μ = a / s := rfl
  have hdecomp : a = s * (a / s) + a % s := (Int.mul_ediv_add_emod a s).symm
  have hr0 : 0 ≤ a % s := Int.emod_nonneg a hsI.ne'
  have hr1 : a % s < s := Int.emod_lt_of_pos a hsI
  have hwa : (((w μ).val : ℤ) + p μ) = a := by simp [ha, wo]; ring
  rw [hwa, hNI] at hv
  have hm : a % (s * n) = s * ((a / s) % n) + a % s := by
    conv_lhs => rw [hdecomp]
    exact int_mod_cell hsI hnI hr0 hr1
  rw [hm] at hv
  rw [hc]
  have : (((iota w p μ).val / s : ℕ) : ℤ) = ((iota w p μ).val : ℤ) / (s : ℤ) := by push_cast; rfl
  rw [this, hv]
  rw [add_comm, Int.add_mul_ediv_left _ _ hsI.ne']
  rw [Int.ediv_eq_zero_of_lt hr0 hr1]; simp

end AdalyFormal.CoverGeom
