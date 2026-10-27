import NVC7
import UMF

/-!
# NVC8 -- the sanity corollary: the proved `SVS.P428Target8Max` (`UnifMax.p428Target8Max_proved`) instantiated at the witness of
`headline_regime_nonvacuousC` (lane nonvac_c_20261017)

For every `ell ≥ 2`, `a > 0`, cube factor `c ≥ 10`, the Max headline's own `m₁, R₁, a₀, γ₀` (chosen before `m, R`), and every `m ≥ m₁`, `R ≥ max R₁ 1`:
there are `k = 2`, `Lu`, a proper three-stratum slab tower `S`, `Λ ≠ ∅`, a curved non-pure-gauge `U` in `ClassCoupled .. c ..`, `α₀ > 0` with `c M α₀ ≤ a₀`,
a nonzero `B̃ ∈ Λ̃`, no class cube wrapping the torus, and the Max conclusion (`WellDefG` and `γ₀ ‖B̃‖² ≤ genForm (C B̃)`) at this witness, with `‖B̃‖² > 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.NonVacC

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem headline_instance_inequalityC (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) (c : ℕ) (hc : 10 ≤ c) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, max R₁ 1 ≤ R →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧ (∃ p, p ∉ S.Om 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
        (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
          IsClassCube ell (ell ^ m) c k S sites j → ∃ x, x ∉ sites) ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hU⟩ := AdalyFormal.UnifMax.p428Target8Max_proved ell hell a ha c hc
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun m hm R hR => ?_⟩
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    headline_regime_nonvacuousC (R := R) hell (le_trans hm₁ hm) hc (le_trans (le_max_right _ _) hR) ha₀
  have hmain := hU m hm R (le_trans (le_max_left _ _) hR) k (by omega) Lu α₀ hα hαS hT S hA Lam hL U hCC
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    hmain.1, hmain.2 Bt h8 h9⟩

end AdalyFormal.NonVacC
