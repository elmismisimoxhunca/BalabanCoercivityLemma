import DK4
import DS2

/-!
# DK5 -- the `hKD` field of `DParts` in the quantifier shape of `DPackage` (KD sub-lane, 2026-10-13)

**`hKD_package`** : for `2 ≤ ℓ` and the room `17ℓ ≤ RM` there is `β₀ = beta0 ℓ > 0` such that on the whole M1 domain of
`DPackage` with `12Mα₀ ≤ β₀` (`TorusOK`, `Admissible`, `LambdaOK2`, `M1Regular`, `0 < α₀`; `CoversOm0p` is not needed), every `B`:
`Σ_e ‖(gparams …).D2in B e‖ ≤ KDfree ℓ · ‖B‖²` (`KDfree ℓ = 2ℓ² K2s ℓ`, DL76) -- the constant is free of `k`, `Lu`, `S`, `Λ`, `U`, `α₀`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DK

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneG (LambdaOK2 gparams)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.DLayer (KDfree)

theorem KDfree_nonneg (ell : ℕ) : 0 ≤ KDfree ell := by
  unfold KDfree AdalyFormal.DLayer.K2s; positivity

theorem hKD_package (ell M R : ℕ) (hell : 0 < ell) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ β₀ →
      TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
      ∀ (U : LinkCfg (scaleUp ell k Lu)), AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      ∀ B : BondFnL2 Lu, ∑ e, ‖((gparams ell k Lu hell S U a Lam).D2in B) e‖ ≤ KDfree ell * ‖B‖ ^ 2 :=
  ⟨beta0 ell, beta0_pos ell hell, fun k Lu α₀ hα hsm hT S hA Lam hL U hU B =>
    D2in_l1_M1' ell M R k Lu hell S U a Lam α₀ hA hell2 hroom hT hL hU hα.le hsm B⟩

#print axioms KDfree_nonneg
#print axioms hKD_package

end AdalyFormal.M1DK
