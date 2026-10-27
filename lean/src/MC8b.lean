import MC8a
import MC1

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC8b -- the sine profile `χ_(x,1) = Ac sin(2π x₀ / N₀)` (all other directions 0): difference identities and bounds.
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

noncomputable def sprof (L : PeriodicLatticeExtent) (Ac : ℝ) (v : ℕ) : ℝ :=
  Ac * Real.sin (2 * Real.pi * (v : ℝ) / ((L 0 + 1 : ℕ) : ℝ))

noncomputable def chiP (L : PeriodicLatticeExtent) (Ac : ℝ) : Bond L → ℝ :=
  fun e => if e.2 = 1 then sprof L Ac (e.1 0).val else 0

/-- the forward difference of the profile at `y` -/
noncomputable def Dd (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) : ℝ :=
  sprof L Ac ((y 0).val + 1) - sprof L Ac (y 0).val

theorem sprof_mod (L : PeriodicLatticeExtent) (Ac : ℝ) (v w : ℕ) (h : v % (L 0 + 1) = w % (L 0 + 1)) :
    sprof L Ac v = sprof L Ac w := by
  unfold sprof
  rw [sin_modEq (L 0 + 1) v w (Nat.succ_pos _) h]

theorem sprof_sh (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) (ν : Fin 3) :
    sprof L Ac ((periodicLatticeShift y ν) 0).val
      = if ν = 0 then sprof L Ac ((y 0).val + 1) else sprof L Ac (y 0).val := by
  rw [shift_coord]
  by_cases h : ν = 0
  · rw [if_pos h.symm, if_pos h]
    exact sprof_mod L Ac _ _ (Nat.mod_mod _ _)
  · rw [if_neg (Ne.symm h), if_neg h]

theorem chiP_diff (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    chiP L Ac (periodicLatticeShift y ν, μ) - chiP L Ac (y, μ)
      = if μ = 1 then (if ν = 0 then Dd L Ac y else 0) else 0 := by
  unfold chiP
  simp only []
  by_cases hμ : μ = 1
  · rw [if_pos hμ, if_pos hμ, if_pos hμ, sprof_sh]
    by_cases hν : ν = 0
    · rw [if_pos hν, if_pos hν]; rfl
    · rw [if_neg hν, if_neg hν]; ring
  · rw [if_neg hμ, if_neg hμ, if_neg hμ]; ring

theorem Dd_abs (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) :
    |Dd L Ac y| ≤ |Ac| * (2 * Real.pi / ((L 0 + 1 : ℕ) : ℝ)) := by
  unfold Dd sprof
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (sin_diff1 (L 0 + 1) _ (Nat.succ_pos _)) (abs_nonneg _)

theorem Dd_shiftBack (L : PeriodicLatticeExtent) (Ac : ℝ) (x : PeriodicLatticeSite L) (ν : Fin 3) :
    |Dd L Ac (periodicLatticeShiftBack x ν) - Dd L Ac x| ≤ |Ac| * (2 * Real.pi / ((L 0 + 1 : ℕ) : ℝ)) ^ 2 := by
  by_cases hν : ν = 0
  · subst hν
    have hsb := AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack x 0
    have hv := congrArg (fun z : PeriodicLatticeSite L => (z 0).val) hsb
    simp only [shift_coord, if_true] at hv
    set a := ((periodicLatticeShiftBack x 0) 0).val with ha
    have hb : (x 0).val = (a + 1) % (L 0 + 1) := hv.symm
    have h1 : sprof L Ac (x 0).val = sprof L Ac (a + 1) := by
      rw [hb]; exact sprof_mod L Ac _ _ (Nat.mod_mod _ _)
    have h2 : sprof L Ac ((x 0).val + 1) = sprof L Ac (a + 2) := by
      apply sprof_mod
      rw [hb]
      exact (Nat.mod_modEq (a + 1) (L 0 + 1)).add_right 1
    unfold Dd
    rw [← ha, h1, h2]
    unfold sprof
    have := sin_diff2 (L 0 + 1) a (Nat.succ_pos _)
    have e : Ac * Real.sin (2 * Real.pi * ((a + 1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ)) -
        Ac * Real.sin (2 * Real.pi * (a : ℝ) / ((L 0 + 1 : ℕ) : ℝ)) -
        (Ac * Real.sin (2 * Real.pi * ((a + 1 + 1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ)) -
        Ac * Real.sin (2 * Real.pi * ((a + 1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ)))
        = Ac * (2 * Real.sin (2 * Real.pi * ((a + 1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ))
          - Real.sin (2 * Real.pi * (a : ℝ) / ((L 0 + 1 : ℕ) : ℝ))
          - Real.sin (2 * Real.pi * ((a + 2 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ))) := by
      have : ((a + 1 + 1 : ℕ) : ℝ) = ((a + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [this]; ring
    rw [e, abs_mul]
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · have h0 : (periodicLatticeShiftBack x ν) 0 = x 0 := by
      unfold periodicLatticeShiftBack
      exact Function.update_of_ne (Ne.symm hν) _ _
    unfold Dd
    rw [h0]
    simp only [sub_self, abs_zero]
    positivity

#print axioms Dd_shiftBack
#print axioms chiP_diff
#print axioms Dd_abs

end AdalyFormal.M0Corollary
