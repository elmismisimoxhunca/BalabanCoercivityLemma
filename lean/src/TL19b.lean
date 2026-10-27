import TL19a

/-!
# TL19b -- `Jf`, `C^{(2)}` on `E₀`
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamily (JSU2Loc)
open AdalyFormal.IngredientFamilyR2

section jdat
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem JfOf_def {L' : PeriodicLatticeExtent} (G : TowerGeom L') (U : Cfg L') :
    (WithLp.toLp 2 (fun b => -(JSU2Loc 1 (plaqIn G.Om0) U b)) : BondFnL2 L') =
      WithLp.toLp 2 (fun b => -(JSU2Loc 1 (plaqIn G.Om0) U b)) := rfl

/-- `Jf` is natural -/
theorem Jf_nat (S : Tower L) (U : Cfg L) :
    (WithLp.toLp 2 (fun b : Bond Lt => -(JSU2Loc 1 (plaqIn (geomOf ell k (towerPull h (fun _ => 0) S)).Om0) (pullCfg h (fun _ => 0) U) b)) : BondFnL2 Lt) =
      liftF (phiE h (fun _ => 0))
        (WithLp.toLp 2 (fun b : Bond L => -(JSU2Loc 1 (plaqIn (geomOf ell k S).Om0) U b)) : BondFnL2 L) := by
  refine PiLp.ext (fun b => ?_)
  show -(JSU2Loc 1 (plaqIn (phiS h (fun _ => 0) ⁻¹' S.Om 0)) (pullCfg h (fun _ => 0) U) b) = -(JSU2Loc 1 (plaqIn (S.Om 0)) U (phiE h (fun _ => 0) b))
  rw [plaqIn_pull h (fun _ => 0), JSU2Loc_nat h (fun _ => 0)]

end jdat

end AdalyFormal.Thin
