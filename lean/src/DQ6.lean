import DQ5

/-!
# DQ6 -- D4 in the exact shape of premise `hC2` of `DParts` (DS1) at `gparams` (sub-builder DQ)

* `hC2_strat` : the field `hC2` of `DParts (gparams ℓ k Lu hell S U a Λ) ω SJ CΨ (K2strat ℓ (12Mα₀)) CW CH1 KD`, for every `a`, `Λ`,
  on the M1 regime with `DQSmall ℓ (12Mα₀)`.
* `hC2_strat_window` : `∀ ℓ ≥ 2, ∃ β₀ > 0, ∃ K2 ≥ 0`, the same field with the amplitude-free `K2` whenever `12Mα₀ ≤ β₀`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1DStrat.DQ

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (M1Regular wnormSq)

theorem hC2_strat (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) (hLu : ∀ μ, ell < Lu μ + 1)
    (hα₀ : 0 ≤ α₀) (hU : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : DQSmall ell (12 * M * α₀)) :
    ∀ z : BondFnL2 (gparams ell k Lu hell S U a Lam).Lf,
      ∑ p, ‖C2fullOf (gparams ell k Lu hell S U a Lam).G (gparams ell k Lu hell S U a Lam).U z p‖
        ≤ K2strat ell (12 * M * α₀) * wnormSq (gparams ell k Lu hell S U a Lam).S (gparams ell k Lu hell S U a Lam).ell
          (gparams ell k Lu hell S U a Lam).k z :=
  fun z => C2full_strat ell M R k Lu S U α₀ hA hell2 hroom hLu hα₀ hU hsm z

theorem hC2_strat_window (ell : ℕ) (hell2 : 2 ≤ ell) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ K2 : ℝ, 0 ≤ K2 ∧
      ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ),
        Admissible ell M R k S → 18 * ell ≤ R * M → (∀ μ, ell < Lu μ + 1) → 0 ≤ α₀ →
        (12 : ℝ) * M * α₀ ≤ β₀ → M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        ∀ z : BondFnL2 (gparams ell k Lu hell S U a Lam).Lf,
          ∑ p, ‖C2fullOf (gparams ell k Lu hell S U a Lam).G (gparams ell k Lu hell S U a Lam).U z p‖
            ≤ K2 * wnormSq (gparams ell k Lu hell S U a Lam).S (gparams ell k Lu hell S U a Lam).ell
              (gparams ell k Lu hell S U a Lam).k z := by
  obtain ⟨β₀, hβ₀, K2, hK2, h⟩ := C2full_strat_window ell hell2
  exact ⟨β₀, hβ₀, K2, hK2, fun M R k Lu _ S U _ _ α₀ hA hroom hLu hα₀ hle hU z =>
    h M R k Lu S U α₀ hA hroom hLu hα₀ hle hU z⟩

#print axioms hC2_strat
#print axioms hC2_strat_window

end AdalyFormal.M1DStrat.DQ
