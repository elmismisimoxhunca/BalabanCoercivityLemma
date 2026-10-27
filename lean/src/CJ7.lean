import CJ5

/-!
# CJ7 -- the statement's own operators read genuine derivatives

For `U` in the class (hypotheses of `CJ4.classRows_QlinB`), at every level `1 ≤ j ≤ k` and every row `b ∈ bondsLam j`:
* `QlinB_row_genuine`: entry `b` of `QlinB (geomOf ell k S) U j A` (the jet `QfullOf` reads) is entry `b` of the GENUINE
  derivative of the printed composite, `e ↦ D(a ↦ qCompX ell Ū j a e)(0)(suCoord A)`;
* `C2rawB_row_genuine`: entry `b` of `C2rawB … j A` (read by `C2fullOf`) is entry `b` of `½ D²(…)(0)(suCoord A, suCoord A)`;
* unit level (`CJ5.classRows_unit`): the second-order row is a genuine second derivative
  (`unit_row_second_order`: `fderiv` of the row is differentiable at `0`, `HasFDerivAt` form).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

theorem QlinB_row_genuine {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j)
    (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) :
    (WithLp.ofLp (QlinB (geomOf ell k S) U j A)) b
      = (WithLp.ofLp (suCoordInv (fun e => fderiv ℝ (fun a : XS (scaleUp ell k Lu) =>
          qCompX ell (bgTower (geomOf ell k S) U) j a e) 0 (suCoord A)))) b := by
  rw [QlinB_apply]
  refine suCoordInv_apply_congr ?_
  exact ((classRows_QlinB hell hroom hS hT hU hsm hj1 hjk hb).2.1 (suCoord A)).symm

theorem C2rawB_row_genuine {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j)
    (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) :
    (WithLp.ofLp (C2rawB (geomOf ell k S) U j A)) b
      = (WithLp.ofLp (suCoordInv (fun e => (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (fun a : XS (scaleUp ell k Lu) =>
          qCompX ell (bgTower (geomOf ell k S) U) j a e)) 0 (suCoord A) (suCoord A)))) b := by
  rw [C2rawB_eq]
  refine suCoordInv_apply_congr ?_
  exact C2CompL_genuine ell _ j b (classRows_QlinB hell hroom hS hT hU hsm hj1 hjk hb) (suCoord A)

/-- `C^∞` at `0` ⇒ the derivative is itself differentiable at `0`: the second-order row is a genuine second derivative. -/
theorem second_order_hasFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : ContDiffAt ℝ ⊤ f 0) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (m := 1) (by simp)
  exact (h1.differentiableAt (by simp)).hasFDerivAt

theorem unit_row_second_order {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hLam : LambdaOK2 ell M R k S Lam)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    (cb : CoarseBond Lu ell) (hc : CRowIn ell Lam cb) :
    HasFDerivAt (fderiv ℝ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)))
      (fderiv ℝ (fderiv ℝ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2))) 0) 0 :=
  second_order_hasFDerivAt (classRows_unit hell0 hell hk hroom hS hT hLam hU hsm cb hc)

#print axioms QlinB_row_genuine
#print axioms C2rawB_row_genuine
#print axioms second_order_hasFDerivAt
#print axioms unit_row_second_order

end AdalyFormal.ClassJets
