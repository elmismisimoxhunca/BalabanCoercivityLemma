import SK1
import AC_Base

/-! AC copy of SK1: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4 (rhoT)
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)

/-- the common shape of the open inputs. `Cs` = constants chosen after `(M, R)`; `Q` constrains them; `P` is the content. -/
def ClassFamAC (ell fc : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ c : Cs, Q (ell ^ m) R c ∧ ∃ s : ℝ, 0 < s ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

end AdalyFormal.M2Skel

