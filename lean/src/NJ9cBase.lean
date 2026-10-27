import NJ9bDrift

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Angle su2NegOne)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice Bond blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.DeltaKR85 (Coeff124.ofPrincipalBackground q124Principal
  q124Principal_eq_unitToCoarseCov_add_delta)
open AdalyFormal.IngredientFamilyR2 (flatCfg RegBg)
open EstimatesLayer.E1E3
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem rhoOf_zero (ell : ℕ) : rhoOf ell 0 = 0 := by unfold rhoOf; simp

theorem e2Majorant_zero : e2Majorant 0 = 0 := by
  simp [e2Majorant, e1Majorant, gInvMajorant]

/-- guard from smallness (all blocks). -/
theorem guard_of_small {ell : ℕ} (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (c : CoarseBond L ell) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1.1 1 ell) :
    loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne := by
  have hδ : 0 ≤ (Real.pi / (2 * Real.sqrt 2)) * ε0 := by positivity
  exact loop_ne_negOne V _ hδ (fun e => (SmallnessBridge.ProdBound.su2Angle_le_frobNorm (V e)).trans
    (mul_le_mul_of_nonneg_left (hV e) (by positivity))) (c.1.1, c.2) x hx hsmall.le


end AdalyFormal.NonflatJet
