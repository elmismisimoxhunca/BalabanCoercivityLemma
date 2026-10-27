import TL22a
import AC_Base

/-!
# AC_Thin -- thin-torus lift lemmas for the hybrid class (lane allc_20261016)

`Thin.geometry_lift`, `Thin.jetReg_of_class`, `Thin.unitReg_of_class` (TL1n, TL22a) are generic in the cube factor `c` but use the ORIGINAL class
`ClassCoupled ell M c k S α η U` (bound factor `c`).  The wrappers below take `ClassCoupledH ell M fc b k S α η U` (any bound factor `b`) and
`ClassSmall ell (b * M * α)`, converting through `α'' = b α / fc` (`bound_eq`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
namespace AdalyFormal.Thin

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.AllC

theorem geometry_liftH {ell M R fc b k : ℕ} {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent}
    (g : GeomLift ell k hell Lut Lu) (hc : 2 ≤ fc)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hCU : ClassCoupledH ell M fc b k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    TorusOK ell M Lut ∧ Admissible ell M R k (liftTower g.fine S) ∧
      LambdaOK2 ell M R k (liftTower g.fine S) (projS g.cover ⁻¹' Lam) ∧
      ClassCoupledH ell M fc b k (liftTower g.fine S) α₀ ((ell : ℝ) ^ k)⁻¹ (liftU g.fine U) := by
  have hfc : 0 < fc := by omega
  obtain ⟨h1, h2, h3, h4⟩ := geometry_lift g hc hT hS hL (hCU.toOrig hfc)
  refine ⟨h1, h2, h3, ?_⟩
  have e := bound_eq (M := M) (b := b) hfc α₀
  exact (ClassCoupledH.congr_bound (b := fc) (b' := b) (α₀ := (b : ℝ) * α₀ / fc) (α₀' := α₀) e).1 h4

theorem jetReg_of_classH {ell M R k fc b : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S)
    (hT : TorusOK ell M Lu) (hfc : 0 < fc) (hU : ClassCoupledH ell M fc b k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : AdalyFormal.ClassJets.ClassSmall ell ((b : ℝ) * M * α₀)) :
    JetReg ell k S (UbarTower su2LogExp ell U) := by
  have e := bound_eq (M := M) (b := b) hfc α₀
  exact jetReg_of_class hell hroom hS hT (hU.toOrig hfc) (by rw [e]; exact hsm)

theorem unitReg_of_classH {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k fc b : ℕ} (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) {α₀ : ℝ}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (hS : Admissible ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S)) (hT : TorusOK ell M Lut)
    (hL : LambdaOK2 ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) (phiS hu (fun _ => 0) ⁻¹' Lam))
    (hfc : 0 < fc)
    (hU : ClassCoupledH ell M fc b k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) α₀ ((ell : ℝ) ^ k)⁻¹
      (pullCfg (covers_scaleUp ell k hell0 hu) (fun _ => 0) U))
    (hsm : AdalyFormal.ClassJets.ClassSmall ell ((b : ℝ) * M * α₀)) :
    UnitReg hu hell0 S U a Lam := by
  have e := bound_eq (M := M) (b := b) hfc α₀
  exact unitReg_of_class hu hell0 S U a Lam hell hk hroom hS hT hL (hU.toOrig hfc) (by rw [e]; exact hsm)

end AdalyFormal.Thin

#print axioms AdalyFormal.Thin.geometry_liftH
#print axioms AdalyFormal.Thin.jetReg_of_classH
#print axioms AdalyFormal.Thin.unitReg_of_classH
