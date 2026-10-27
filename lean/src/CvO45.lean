import CvO44

/-!
# CvO45 -- the (0,1)-plaquette weight of `Delta_loc` along the staggered path depends on `x₀` only (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- the (0,1)-plaquette at `x` lies in `plaqIn {z | J z₀}` iff `x₀` and its successor satisfy `J`. -/
theorem plaqIn_01_iff (J : ℕ → Prop) (x : PeriodicLatticeSite L) :
    (x, q01) ∈ plaqIn {z : PeriodicLatticeSite L | J (z 0).val} ↔ J (x 0).val ∧ J (nxt (L 0) (x 0).val) := by
  have A : ((periodicLatticeShift x 0) 0).val = nxt (L 0) (x 0).val := val_shift0 x
  have B : ((periodicLatticeShift (periodicLatticeShift x 0) 1) 0).val = nxt (L 0) (x 0).val := by
    rw [shift_coord_ne _ 1 0 (by decide), A]
  have C : ((periodicLatticeShift (periodicLatticeShift x 1) 0) 0).val = nxt (L 0) (x 0).val := by
    rw [val_shift0, shift_coord_ne x 1 0 (by decide)]
  have D : ((periodicLatticeShift x 1) 0).val = (x 0).val := by
    rw [shift_coord_ne x 1 0 (by decide)]
  unfold plaqIn
  simp only [q01, periodicPlaquetteBoundaryEdges, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, A, B, C, D]
  tauto

open Classical in
/-- the (0,1)-plaquette weight along the staggered path as a function of `x₀`. -/
noncomputable def omegaW (J : ℕ → Prop) (N0 c : ℕ) (t : ℝ) (v : ℕ) : ℝ :=
  if J v ∧ J (nxt N0 v) then Real.cos (t * ((if nxt N0 v = c then 1 else 0) - (if v = c then 1 else 0))) else 0

open Classical in
theorem hω_stag (J : ℕ → Prop) (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L) :
    (if (x, q01) ∈ plaqIn {z : PeriodicLatticeSite L | J (z 0).val} then holCos (stagCfg c t : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x, q01) else 0) =
      omegaW J (L 0) c t (x 0).val := by
  unfold omegaW
  by_cases h : J (x 0).val ∧ J (nxt (L 0) (x 0).val)
  · rw [if_pos ((plaqIn_01_iff J x).mpr h), if_pos h, holCos_stag]
    congr 2
    simp only [layerEps, q01, if_true, val_shift0]
  · rw [if_neg (fun h' => h ((plaqIn_01_iff J x).mp h')), if_neg h]

#print axioms plaqIn_01_iff
#print axioms hω_stag

end AdalyFormal.CoverOmega
