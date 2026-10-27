import NV7
import RI6

/-!
# NV8 -- the sanity corollary: the proved headline `p428Target8`, instantiated at the witness of `headline_regime_nonvacuous` (lane nonvac_20261015)

For every `ell ≥ 2`, `a > 0`, the headline's own `m₀`, `R₀`, `a₀`, `γ₀` (taken from `AdalyFormal.M2RightInv.p428Target8`) and every `m ≥ m₀`, `R ≥ max R₀ 18`:
there are `k = 2`, `Lu`, a proper three-stratum slab tower `S`, `Λ ≠ ∅`, a curved non-pure-gauge `U` in `ClassCoupled`, `α₀ > 0` with `12 M α₀ ≤ a₀`,
and a nonzero `B̃ ∈ Λ̃` such that `γ₀ ‖B̃‖² ≤ genForm (C B̃)` at this witness, with `‖B̃‖² > 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.NonVac

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem headline_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
        0 < α₀ ∧ ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧ (∃ p, p ∉ S.Om 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₀, hm₀, hm⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨max R₀ 18, fun R hR' => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ₀, hall⟩ := hR R (le_trans (le_max_left _ _) hR')
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    headline_regime_nonvacuous hell (le_trans hm₀ hm') (le_trans (le_max_right _ _) hR') ha₀
  refine ⟨a₀, γ₀, ha₀, hγ₀, k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, ?_⟩
  exact hall k (by omega) Lu α₀ hα hαS hT S hA Lam hL U hCC Bt h8 h9

end AdalyFormal.NonVac
