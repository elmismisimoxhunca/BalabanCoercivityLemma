import TL19b

/-!
# TL19c -- `C^{(2)}` on `E₀` (function level) for the concrete base data
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section c2e
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ} [Nonempty (DeckIdx Lt L)]

theorem C2full_E1 (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) (z : BondFnL2 L) :
    C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) ((covE h).ell z) =
      (covBIdx h S hp hell).ell (C2fullOf (geomOf ell k S) U z) := by
  refine PiLp.ext (fun p => ?_)
  show C2fullOf _ _ (liftF (covE h).π z) p = liftF (covBIdx h S hp hell).π (C2fullOf (geomOf ell k S) U z) p
  rw [covE_pi, covBIdx_pi h hp hell S, liftF_apply]
  exact C2fullOf_nat h hp hell S U _ rfl _ rfl hreg (bHφ_pi h hp hell S) z p

theorem C2full_equi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) (d : DeckIdx Lt L) (z : BondFnL2 Lt) :
    C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) ((covE h).pull d z) =
      (covBIdx h S hp hell).pull d (C2fullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) z) := by
  refine PiLp.ext (fun p => ?_)
  show C2fullOf _ _ (liftF ((covE h).τ d) z) p = liftF ((covBIdx h S hp hell).τ d) (C2fullOf _ _ z) p
  have e1 : ((covE h).τ d : Bond Lt → Bond Lt) = phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) := covE_tau h d
  have e2 := covBIdx_tau h hp hell S d
  rw [e1, liftF_apply, e2]
  exact C2fullOf_nat (Covers.refl Lt) (phiOK_tau h hp d) hell (towerPull h (fun _ => 0) S) (pullCfg h (fun _ => 0) U)
    (towerPull h (fun _ => 0) S) (towerPull_tau h S d).symm (pullCfg h (fun _ => 0) U) (pullCfg_tau h d U).symm
    hreg (bHφ_tau h hp hell S d) z p

end c2e

end AdalyFormal.Thin
