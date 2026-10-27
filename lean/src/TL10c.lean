import TL10b

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section rp
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

open Classical in
theorem desc_Rproj [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) :
    Desc (covS h) (covS h) (Rproj (geomOf ell k S) U)
      (Rproj (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :=
  desc_starProjection (covS h) (lapDir (geomOf ell k S) U)
    (lapDir (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) (desc_lapDir h S U)
    (NQp (geomOf ell k S) U) (NQp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U))
    (fun f hf => nqp_ell h hp hell S U f hf) (fun f hf => nqp_sig h hp hell S U f hf)
    (fun d f hf => nqp_pull h hp hell S U d f hf)
    (RImage (geomOf ell k S) U) (RImage (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U))
    (fun w => by unfold RImage; simp [Submodule.mem_map]) (fun w => by unfold RImage; simp [Submodule.mem_map])

open Classical in
theorem desc_Tfull [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) :
    Desc (covE h) (covS h) (Tfull (geomOf ell k S) U)
      (Tfull (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :=
  (desc_gradAdj h U).comp (desc_Rproj h hp hell S U)

open Classical in
theorem desc_Gp [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
      (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0))) :
    IsUnit (DelpA (geomOf ell k S) U a + (1 - siteMask (geomOf ell k S).Om0)) ∧
    Desc (covS h) (covS h) (Gp (geomOf ell k S) U a)
      (Gp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a) := by
  have hd : Desc (covS h) (covS h) (DelpA (geomOf ell k S) U a + (1 - siteMask (geomOf ell k S).Om0))
      (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
        (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0)) :=
    (desc_DelpA h hp hell S U a).add (Desc.id.sub (desc_siteMask h (S.Om 0)))
  obtain ⟨hu', hinv⟩ := hd.inverse hu
  exact ⟨hu', (desc_siteMask h (S.Om 0)).comp hinv⟩

end rp

end AdalyFormal.Thin
