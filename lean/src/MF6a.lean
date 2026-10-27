import NJ2Jet
import NJ3Base
import ZXR2Unit1

/-!
# MF6a (TEXT COPY of nonflat_jet R5Q1, recompiled against the r7 fork) -- the r5 statement-lane carrier (`ZXR2Unit1`; touching-row `Dset` lives in `ZXR2Unit2`): `Q1jet` IS `q124Principal 1 ell V0`.
(`ZXR2Unit1` is textually `R2Unit1` with the r5 imports; the lemma is the same as `NonflatJet.Q1jet_eq_q124`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.M0Finish.R7

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonflatJet (bondToUnit fderiv_qStepX_one_apply)

variable {L : PeriodicLatticeExtent}

theorem fineDir_suCoordF (B : Bond L → SuTwo) :
    fineDirToUnitBond (fun e => toM2 (suCoordF B e)) (fun e => (toM2_mem (suCoordF B e)).1)
        (fun e => (toM2_mem (suCoordF B e)).2) = bondToUnit B := by
  funext b
  apply Subtype.ext
  show toM2 (fromM2 ((B (b.1.1, b.2) : SuTwo) : M2)) = _
  exact toM2_fromM2 (B (b.1.1, b.2)).2

theorem Q1jet_eq_q124 (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hreg : RegBg 1 ell V0)
    (hnc : ∀ c : CoarseBond L ell, ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V0 (c.1.1, c.2) x ≠ su2NegOne)
    (B : Bond L → SuTwo) (c : CoarseBond L ell) :
    Q1jet ell V0 B c
      = q124Principal 1 ell V0 (bondToUnit B)
          (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond L (1 * ell)) := by
  have hj := fderiv_qStepX_one_apply V0 ell hreg (c.1.1, c.2) c.1.2 hell hdvd (hnc c)
    (suCoordF B)
  rw [fineDir_suCoordF] at hj
  -- r8 transfer patch (bridge `Q1jet_eq_r7`, RegBg 1 ell V0 = `hreg`)
  rw [Q1jet_eq_r7 ell V0 hreg B c]
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepX 1 ell V0 (suCoordF B))) (c.1.1, c.2) = _
  apply Subtype.ext
  have hmem := (q124Principal 1 ell V0 (bondToUnit B)
    (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond L (1 * ell))).2
  have hl : (QlinStepX 1 ell V0 (suCoordF B)) (c.1.1, c.2)
      = (ell : ℝ) • fromM2 ((q124Principal 1 ell V0 (bondToUnit B)
          (⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩ : CoarseBond L (1 * ell)) : SuTwo) : M2) := hj
  show ((ell : ℝ)⁻¹) • toM2 ((QlinStepX 1 ell V0 (suCoordF B)) (c.1.1, c.2)) = _
  rw [hl, map_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hell.ne'), one_smul]
  exact toM2_fromM2 hmem

#print axioms Q1jet_eq_q124

end AdalyFormal.M0Finish.R7
