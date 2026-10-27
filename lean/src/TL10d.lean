import TL10c

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section wp
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem plaqIn_pull (o : Fin 3 → ℕ) (S : Set (PeriodicLatticeSite L)) :
    plaqIn (phiS h o ⁻¹' S) = phiP h o ⁻¹' plaqIn S := by
  ext p
  simp only [plaqIn, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro hp e he
    rw [edge_mem'] at he
    rcases he with rfl | rfl | rfl | rfl
    · have := hp (p.1, p.2.1.1) ((edge_mem' _ _).mpr (Or.inl rfl)); simpa [phiP, phiS_shift] using this
    · have := hp (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ((edge_mem' _ _).mpr (Or.inr (Or.inl rfl)))
      simpa [phiP, phiS_shift] using this
    · have := hp (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl rfl))))
      simpa [phiP, phiS_shift] using this
    · have := hp (p.1, p.2.1.2) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))); simpa [phiP, phiS_shift] using this
  · intro hp e he
    rw [edge_mem'] at he
    rcases he with rfl | rfl | rfl | rfl
    · have := hp (phiE h o (p.1, p.2.1.1)) ((edge_mem' _ _).mpr (Or.inl rfl)); simpa [phiP, phiE, phiS_shift] using this
    · have := hp (phiE h o (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) ((edge_mem' _ _).mpr (Or.inr (Or.inl (by simp [phiP, phiE, phiS_shift]))))
      simpa [phiP, phiE, phiS_shift] using this
    · have := hp (phiE h o (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl (by simp [phiP, phiE, phiS_shift])))))
      simpa [phiP, phiE, phiS_shift] using this
    · have := hp (phiE h o (p.1, p.2.1.2)) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr (by simp [phiP, phiE])))))
      simpa [phiP, phiE, phiS_shift] using this

open Classical in
theorem desc_Delta [Nonempty (DeckIdx Lt L)] (S : Tower L) (U : Cfg L) :
    Desc (covE h) (covE h) (Delta (geomOf ell k S) U)
      (Delta (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) := by
  have := desc_deltaKLoc h U (plaqIn (geomOf ell k S).Om0)
  unfold Delta
  have e : plaqIn (geomOf ell k (towerPull h (fun _ => 0) S)).Om0 = phiP h (fun _ => 0) ⁻¹' plaqIn (geomOf ell k S).Om0 :=
    plaqIn_pull h (fun _ => 0) _
  rw [e]
  exact this

open Classical in
theorem desc_Wop [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
      (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0))) :
    Desc (covE h) (covE h) (Wop (geomOf ell k S) U a)
      (Wop (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a) := by
  unfold Wop
  exact Desc.id.sub ((((desc_gradAdj h U).comp (desc_Rproj h hp hell S U)).comp (desc_Gp h hp hell S U a hu).2).comp (desc_gradL2 h U))

open Classical in
theorem desc_DpiFull [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
      (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0))) :
    Desc (covE h) (covE h) (DpiFull (geomOf ell k S) U a)
      (DpiFull (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a) := by
  unfold DpiFull
  exact ((desc_Wop h hp hell S U a hu).comp (desc_Delta h S U)).comp (desc_Wop h hp hell S U a hu).adjoint

end wp


end AdalyFormal.Thin
