import MC8d

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.CurvBlock (dv)

/-- the sine field has a plaquette (directions `(0,1)` at the origin) with `dv > 0` -/
theorem sine_curved (L : PeriodicLatticeExtent) (Ac η : ℝ) (hAc0 : 0 < Ac) (hAc1 : Ac < 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hN : 3 ≤ L 0 + 1) :
    ∃ p : PeriodicLatticePlaquette L, 0 < dv (periodicPlaquetteHolonomy (Ufield η (chiP L Ac)) p) := by
  let y : PeriodicLatticeSite L := fun μ => ⟨0, Nat.succ_pos _⟩
  have hy0 : (y 0).val = 0 := rfl
  refine ⟨(y, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩), ?_⟩
  have hs : sprof L Ac ((periodicLatticeShift y 0) 0).val = sprof L Ac 1 := by
    rw [sprof_sh, if_pos rfl, hy0]
  have e1 : chiP L Ac (y, 0) = 0 := by simp [chiP]
  have e2 : chiP L Ac (periodicLatticeShift y 0, 1) = sprof L Ac 1 := by
    simp only [chiP, if_true]; exact hs
  have e3 : chiP L Ac (periodicLatticeShift y 1, 0) = 0 := by simp [chiP]
  have e4 : chiP L Ac (y, 1) = 0 := by
    simp only [chiP, if_true, hy0]; simp [sprof]
  have hhol : periodicPlaquetteHolonomy (Ufield η (chiP L Ac)) (y, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)
      = Ug (η * sprof L Ac 1) := by
    show Ufield η (chiP L Ac) (y, 0) * Ufield η (chiP L Ac) (periodicLatticeShift y 0, 1)
        * (Ufield η (chiP L Ac) (periodicLatticeShift y 1, 0))⁻¹ * (Ufield η (chiP L Ac) (y, 1))⁻¹ = _
    simp only [Ufield, e1, e2, e3, e4, mul_zero, Ug_zero, inv_one, mul_one, one_mul]
  rw [hhol]
  apply dv_pos_of_entry
  have hNr : (3 : ℝ) ≤ ((L 0 + 1 : ℕ) : ℝ) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hang : 0 < 2 * Real.pi * ((1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ) := by positivity
  have hang2 : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ) < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]; simp only [Nat.cast_one]; nlinarith
  have hsin := Real.sin_pos_of_pos_of_lt_pi hang hang2
  have hsin1 := Real.sin_le_one (2 * Real.pi * ((1 : ℕ) : ℝ) / ((L 0 + 1 : ℕ) : ℝ))
  apply Ug_ne_one
  · unfold sprof; positivity
  · unfold sprof
    calc η * (Ac * Real.sin _) ≤ 1 * (Ac * 1) := by
          apply mul_le_mul hη1 _ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hsin1 hAc0.le
      _ < 1 := by linarith

#print axioms sine_curved

end AdalyFormal.M0Corollary
