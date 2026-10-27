import TL14a

/-!
# TL14b -- the linear parts of `baseData` on `E₀` descend
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section base
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ} [Nonempty (DeckIdx Lt L)]

noncomputable abbrev cB : HCov (DeckIdx Lt L) (BondFnL2 L) (BondFnL2 Lt) := (covE h).toH (E := SuTwo)
noncomputable abbrev cSite : HCov (DeckIdx Lt L) (SiteL2 L) (SiteL2 Lt) := (covS h).toH (E := SuTwo)

theorem hdesc_pE (S : Tower L) :
    HDesc (cB h) (hE0 (ell := ell) (k := k) h S) (pE (geomOf ell k S)) (pE (geomOf ell k (towerPull h (fun _ => 0) S))) :=
  (hdesc_iE (ell := ell) (k := k) h S).adjoint

theorem hdesc_Dpi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
      (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0))) :
    HDesc (hE0 (ell := ell) (k := k) h S) (hE0 (ell := ell) (k := k) h S)
      ((pE (geomOf ell k S)).comp ((DpiFull (geomOf ell k S) U a).comp (iE (geomOf ell k S))))
      ((pE (geomOf ell k (towerPull h (fun _ => 0) S))).comp
        ((DpiFull (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a).comp
          (iE (geomOf ell k (towerPull h (fun _ => 0) S))))) :=
  ((hdesc_iE (ell := ell) (k := k) h S).comp (desc_DpiFull h hp hell S U a hu).toH).comp (hdesc_pE h S)

theorem hdesc_T (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) :
    HDesc (hE0 (ell := ell) (k := k) h S) (cSite h)
      ((Tfull (geomOf ell k S) U).comp (iE (geomOf ell k S)))
      ((Tfull (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)).comp
        (iE (geomOf ell k (towerPull h (fun _ => 0) S)))) :=
  (hdesc_iE (ell := ell) (k := k) h S).comp (desc_Tfull h hp hell S U).toH

noncomputable abbrev cFSp (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) :
    HCov (DeckIdx Lt L) (FSp (geomOf ell k S)) (FSp (geomOf ell k (towerPull h (fun _ => 0) S))) :=
  (covBIdx h S hp hell).toH (E := SuTwo)

theorem diagW_eq_diagOp {L' : PeriodicLatticeExtent} (G : TowerGeom L') (w : BIdx G → ℝ) :
    diagW G w = diagOp (E := SuTwo) w := rfl

open Classical in
theorem hdesc_Qfull (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) :
    HDesc (cB h) (cFSp h hp hell S) (QfullOf (geomOf ell k S) U)
      (QfullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :=
  (desc_QfullOf h hp hell S U hreg).toH

open Classical in
theorem hdesc_Q (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) :
    HDesc (hE0 (ell := ell) (k := k) h S) (cFSp h hp hell S)
      ((QfullOf (geomOf ell k S) U).comp (iE (geomOf ell k S)))
      ((QfullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)).comp
        (iE (geomOf ell k (towerPull h (fun _ => 0) S)))) :=
  (hdesc_iE (ell := ell) (k := k) h S).comp (hdesc_Qfull h hp hell S U hreg)

open Classical in
theorem hdesc_MassFull (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) :
    HDesc (cB h) (cB h)
      (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U))
      (MassFull (geomOf ell k (towerPull h (fun _ => 0) S)) a
        (bondSectorOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U))) := by
  unfold MassFull
  have hdiag : HDesc (cFSp h hp hell S) (cFSp h hp hell S)
      (diagW (geomOf ell k S) (massW (geomOf ell k S) a))
      (diagW (geomOf ell k (towerPull h (fun _ => 0) S)) (massW (geomOf ell k (towerPull h (fun _ => 0) S)) a)) := by
    rw [diagW_eq_diagOp, diagW_eq_diagOp]
    exact (desc_diagOp (covBIdx h S hp hell) (massW (geomOf ell k S) a)).toH
  exact ((hdesc_Qfull h hp hell S U hreg).comp hdiag).comp (hdesc_Qfull h hp hell S U hreg).adjoint

open Classical in
theorem hdesc_Mass (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) :
    HDesc (hE0 (ell := ell) (k := k) h S) (hE0 (ell := ell) (k := k) h S)
      ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S))))
      ((pE (geomOf ell k (towerPull h (fun _ => 0) S))).comp
        ((MassFull (geomOf ell k (towerPull h (fun _ => 0) S)) a
          (bondSectorOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U))).comp
          (iE (geomOf ell k (towerPull h (fun _ => 0) S))))) :=
  ((hdesc_iE (ell := ell) (k := k) h S).comp (hdesc_MassFull h hp hell S U a hreg)).comp (hdesc_pE h S)

end base


end AdalyFormal.Thin
