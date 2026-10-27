import PP9
import OGP0

/-!
# SG11 -- F3 assembled: `massComm_of_charts12` (lane m2_fields123_20261015)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.OneGap12

open AdalyFormal.M2F123
open AdalyFormal.OneGap12

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneR8 (rhoT)
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.NonflatJet

variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **F3 from per-row charts.**  The SK1 field `MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀)))`. -/
theorem massComm_of_charts12 (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR1 : 1 ≤ R)
    (hR8 : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 < α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)))) < r0)
    (a : ℝ) (ha : 0 ≤ a) (U : LinkCfg (scaleUp ell k Lu))
    (hch : ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) → AnchorChart12 ell M k S U α₀ η p.2.1.1 (rhoT ell p.1)) :
    MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (AdalyFormal.M2Skel.alpha1 ell α₀))) := by
  have hq : ∀ p : BIdx (geomOf ell k S), RowQ ell k Lu S U (SstarM ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀))) p := by
    intro p
    by_cases h1 : 1 ≤ (p.1 : ℕ)
    · exact rowQ_of_chart12 hell2 hS hroom hT3 hη hα.le ha1 hsm4 hsmA hrr U p (hch p h1)
    · exact rowQ_level012 hell2 hS hroom hM hT3 hη hα ha1 hsm4 hsmA hrr U p (by omega)
  exact massComm_of_rowQ hS (by norm_num) hM hell2 hR1 (by omega) (le_refl 5) U _ hq a ha

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.massComm_of_charts12
