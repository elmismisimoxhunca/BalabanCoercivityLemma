import TL19c

/-!
# TL20a -- the descent datum `BDLink` of the genuine `baseData` of the statement
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamily (JSU2Loc)
open AdalyFormal.IngredientFamilyR2

section bdl
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ} [Nonempty (DeckIdx Lt L)]

/-- the source `J` on the fine torus -/
noncomputable def JfG {L' : PeriodicLatticeExtent} (G : TowerGeom L') (U : Cfg L') : BondFnL2 L' :=
  WithLp.toLp 2 (fun b => -(JSU2Loc 1 (plaqIn G.Om0) U b))

theorem JfG_nat (S : Tower L) (U : Cfg L) :
    JfG (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) = liftF (phiE h (fun _ => 0)) (JfG (geomOf ell k S) U) :=
  Jf_nat h S U

theorem bdlink_base (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U)))
    (hu : IsUnit (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a +
      (1 - siteMask (geomOf ell k (towerPull h (fun _ => 0) S)).Om0))) :
    BDLink (Dd := DeckIdx Lt L)
      (baseData (geomOf ell k S) U a (bondSectorOf (geomOf ell k S) U) (JfG (geomOf ell k S) U))
      (baseData (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a
        (bondSectorOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U))
        (JfG (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)))
      (hE0 (ell := ell) (k := k) h S) (cSite h) (cFSp h hp hell S) := by
  refine ⟨hdesc_Dpi h hp hell S U a hu, hdesc_T h hp hell S U, hdesc_Q h hp hell S U hreg, hdesc_Mass h hp hell S U a hreg, ?_, ?_, ?_⟩
  · show pE (geomOf ell k (towerPull h (fun _ => 0) S)) (JfG _ _) = (hE0 (ell := ell) (k := k) h S).ell (pE (geomOf ell k S) (JfG _ _))
    rw [JfG_nat h S U]
    have := congrArg (fun T => T (JfG (geomOf ell k S) U)) (hdesc_pE (ell := ell) (k := k) h S).e1
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]
    show _ = pE _ ((covE h).ell _)
    rw [Cov.ell]
    rw [covE_pi]
  · intro A
    have hW := (desc_Wop h hp hell S U a hu).e1
    show C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)
        (Wop (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a ((covE h).ell (iE (geomOf ell k S) A))) =
      (covBIdx h S hp hell).ell (C2fullOf (geomOf ell k S) U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) A)))
    have hw := congrArg (fun T => T (iE (geomOf ell k S) A)) hW
    simp only [ContinuousLinearMap.comp_apply] at hw
    rw [hw]
    exact C2full_E1 h hp hell S U hreg _
  · intro d A
    have hW := (desc_Wop h hp hell S U a hu).equi d
    show C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)
        (Wop (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a ((covE h).pull d (iE _ A))) =
      (covBIdx h S hp hell).pull d (C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)
        (Wop (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a (iE _ A)))
    have hw := congrArg (fun T => T (iE (geomOf ell k (towerPull h (fun _ => 0) S)) A)) hW
    simp only [ContinuousLinearMap.comp_apply] at hw
    rw [hw]
    exact C2full_equi h hp hell S U hreg d _

end bdl

end AdalyFormal.Thin
