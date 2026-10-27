import D1Eval2

/-!
# D1Geo1 -- holonomies of `U_θ` on the four plaquettes of the boundary bond `(x,0)` of `Ω₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)

variable {L : PeriodicLatticeExtent}

/-- `x` is a boundary site of the slab-like region `Om` in direction `0`. -/
structure BdPt (Om : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) : Prop where
  hx : x ∈ Om
  hx' : periodicLatticeShift x 0 ∉ Om
  trans : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om)
  side : ∀ ν : Fin 3, periodicLatticeShift x ν ≠ x

theorem Uth_in (Om : Set (PeriodicLatticeSite L)) (θ : ℝ) (e : Bond L) (he : e.1 ∈ Om) : Uth Om θ e = 1 := by
  unfold Uth
  rw [if_neg (fun h => h.1 he)]

theorem Uth_Z (Om : Set (PeriodicLatticeSite L)) (θ : ℝ) (e : Bond L) (he : e ∈ Zb Om) : Uth Om θ e = uθ θ := by
  unfold Uth
  rw [if_pos he]

variable {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}

theorem BdPt.shiftBack_mem (h : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) :
    periodicLatticeShiftBack x ν.1 ∈ Om := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  rw [← h.trans _ ν.1 hν, periodicLatticeShift_shiftBack]
  exact h.hx

theorem BdPt.holonomy1 (h : BdPt Om x) (θ : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (Uth Om θ) (P1 x ν) = uθ θ := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have e1 : Uth Om θ (x, (0 : Fin 3)) = 1 := Uth_in Om θ _ h.hx
  have e2 : Uth Om θ (periodicLatticeShift x 0, ν.1) = uθ θ := by
    refine Uth_Z Om θ _ ⟨h.hx', ?_⟩
    intro hm
    exact h.hx' ((h.trans _ ν.1 hν).mp hm)
  have e3 : Uth Om θ (periodicLatticeShift x ν.1, (0 : Fin 3)) = 1 :=
    Uth_in Om θ _ ((h.trans _ ν.1 hν).mpr h.hx)
  have e4 : Uth Om θ (x, ν.1) = 1 := Uth_in Om θ _ h.hx
  show periodicPlaquetteHolonomy (Uth Om θ) (P1 x ν) = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [e1, e2, e3, e4]
  simp

theorem BdPt.holonomy2 (h : BdPt Om x) (θ : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (Uth Om θ) (P2 x ν) = uθ θ := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have hy := h.shiftBack_mem ν
  have e1 : Uth Om θ (periodicLatticeShiftBack x ν.1, (0 : Fin 3)) = 1 := Uth_in Om θ _ hy
  have hsh : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 = periodicLatticeShift x 0 := by
    rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
  have hz : periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0 ∉ Om := by
    intro hm
    apply h.hx'
    rw [← hsh]
    exact (h.trans _ ν.1 hν).mpr hm
  have e2 : Uth Om θ (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0, ν.1) = uθ θ := by
    refine Uth_Z Om θ _ ⟨hz, ?_⟩
    show periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 ∉ Om
    rw [hsh]; exact h.hx'
  have e3 : Uth Om θ (periodicLatticeShift (periodicLatticeShiftBack x ν.1) ν.1, (0 : Fin 3)) = 1 := by
    rw [periodicLatticeShift_shiftBack]; exact Uth_in Om θ _ h.hx
  have e4 : Uth Om θ (periodicLatticeShiftBack x ν.1, ν.1) = 1 := Uth_in Om θ _ hy
  show periodicPlaquetteHolonomy (Uth Om θ) (P2 x ν) = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [e1, e2, e3, e4]
  simp

theorem BdPt.hU2 (h : BdPt Om x) (θ : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    Uth Om θ (periodicLatticeShiftBack x ν.1, ν.1) = 1 := Uth_in Om θ _ (h.shiftBack_mem ν)

/-- **the literal form at `θ = π`**: `⟨A, Δ_lit(U_π) A⟩ = -4⟨X,X⟩` for `A = X δ_{(x,0)}`. -/
theorem BdPt.delta_pi (h : BdPt Om x) (X : AdalyFormal.Balaban.CovariantOperators.SuTwo) :
    (inner ℝ (sing (x, (0 : Fin 3)) X) (AdalyFormal.StatementLaneR6.deltaKLocCLM (Uth Om Real.pi) (Set.univ : Set (PeriodicLatticePlaquette L)) (sing (x, (0 : Fin 3)) X)) : ℝ)
      = -4 * AdalyFormal.Balaban.SuTwoInner.hsInner X X := by
  refine delta_value (Uth Om Real.pi) x X h.side ?_ ?_ (h.hU2 Real.pi)
  · intro ν; rw [h.holonomy1]; exact uθ_pi_coe
  · intro ν; rw [h.holonomy2]; exact uθ_pi_coe

#print axioms BdPt.delta_pi

end AdalyFormal.D1Literal
