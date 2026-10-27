import NJ9Drift

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
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.DeltaKR85 (Coeff124.ofPrincipalBackground q124Principal
  q124Principal_eq_unitToCoarseCov_add_delta)
open AdalyFormal.IngredientFamilyR2 (flatCfg RegBg one_mem_LogReg hol_flat)
open EstimatesLayer.E1E3
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem loopVar_flat (ell : ℕ) (c : AdalyFormal.Target.ClayStatement.PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    loopVar 1 ell (flatCfg : PeriodicLinkConfiguration SU2 L) c x = 1 := by
  unfold loopVar gammaVarStrided coarseBondVar
  rw [hol_flat, hol_flat, hol_flat, hol_flat]
  simp

theorem regBg_flat (ell : ℕ) : RegBg 1 ell (flatCfg : PeriodicLinkConfiguration SU2 L) := by
  intro c x _
  rw [loopVar_flat]
  exact one_mem_LogReg

theorem flatCfg_eq_trivialU : (flatCfg : PeriodicLinkConfiguration SU2 L) = trivialU L := rfl

#print axioms regBg_flat

end AdalyFormal.NonflatJet
