import CvOF2
import CvOI6
import CvOH5
import CvO35

/-!
# CvOF3 -- `Qs` on Z-rows, `Q` on Z-fields, at the level of the base data (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `Qs` of a Z-row field is the Z-field `zfield (Wt rho)` (given that it lies in `E_0`). -/
theorem Qs_zrow {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < Real.pi)
    (a : ℝ) (Jf : BondFnL2 L) (ρ : ℕ → ℕ → ℝ) (hmem : (zfield (Wt ell isRow ρ) : BondFnL2 L) ∈ bondSupp G) :
    (((baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Qs (zrow G ρ) : ↥(bondSupp G)) : BondFnL2 L) = zfield (Wt ell isRow ρ) := by
  have : (baseData G (stagCfg c t) a (bondSectorOf G (stagCfg c t)) Jf).Qs (zrow G ρ) = ⟨zfield (Wt ell isRow ρ), hmem⟩ := by
    apply ext_inner_left ℝ
    intro w
    show (inner ℝ w ((ContinuousLinearMap.adjoint ((bondSectorOf G (stagCfg c t)).Qfull.comp (iE G))) (zrow G ρ)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    show (inner ℝ ((QfullOf G (stagCfg c t)) (iE G w)) (zrow G ρ) : ℝ) = _
    rw [inner_Q_zrow S t htπ]
    rfl
  rw [this]

#print axioms Qs_zrow

end AdalyFormal.CoverOmega
