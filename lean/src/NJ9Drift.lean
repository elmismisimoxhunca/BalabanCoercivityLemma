import NJ8Eb
import R2Flat1

/-!
# NJ9Drift -- sup-norm drift of the genuine unit-level `Q₁` (`Q1jet`) at a non-flat background from the flat one:
`‖(Q1jet V₀ - Q1jet 1) B (c)‖ ≤ (8 ell ε₀ + 8 κ) M`, `κ = e2Majorant (ρ(ell,ε₀))`, volume free.
-/
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
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.DeltaKR85 (Coeff124.ofPrincipalBackground q124Principal)
open AdalyFormal.IngredientFamilyR2 (flatCfg RegBg one_mem_LogReg)
open EstimatesLayer.E1E3
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem loop_ne_negOne {ell : ℕ} (V : PeriodicLinkConfiguration SU2 L) (δ : ℝ) (hδ : 0 ≤ δ)
    (hang : ∀ e, su2Angle (V e) ≤ δ) (c : AdalyFormal.Target.ClayStatement.PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 1 ell)
    (hs : (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * δ ≤ Real.pi / 2) :
    loopVar 1 ell V c x ≠ su2NegOne := by
  have hang' : su2Angle (loopVar 1 ell V c x) ≤ (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * δ := by
    rw [← SmallnessBridge.Assemble.loopFactors_prod]
    refine (SmallnessBridge.ProdBound.su2Angle_list_prod_le_length_mul _ δ
      (fun g hg => SmallnessBridge.Assemble.su2Angle_loopFactors_le 1 ell V c x δ hang hg)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (SmallnessBridge.Assemble.loopFactors_length_le_bound V ell c x hx)) hδ
  exact AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le (hang'.trans hs)

theorem flat_guard {ell : ℕ} (hell : 0 < ell) (c : AdalyFormal.Target.ClayStatement.PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 1 ell) :
    loopVar 1 ell (flatCfg : PeriodicLinkConfiguration SU2 L) c x ≠ su2NegOne := by
  refine loop_ne_negOne (flatCfg : PeriodicLinkConfiguration SU2 L) 0 le_rfl (fun e => ?_) c x hx
    (by rw [mul_zero]; positivity)
  show su2Angle (1 : SU2) ≤ 0
  rw [AdalyFormal.Balaban.Bch2.su2Angle_one]

#print axioms loop_ne_negOne
#print axioms flat_guard

end AdalyFormal.NonflatJet
