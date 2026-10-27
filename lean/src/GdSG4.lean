import GdSG3

/-!
# GdSG4 -- `GapAt` and the guarded literal inequality on the boundary-twist family, in the regime of the proved localised chain.

* `InstIneqSG_twist`: pointwise (guard gap + full-guard inequality).
* `SG_on_twist_family`: the shape of `P428Target8SG selAll sJ`, restricted to the configurations `U_θ = Uth (Ω₀) θ`, on thick tori with `Λ ≠ ∅`.
* `SG_on_twist_family_nv`: the NV three-stratum slab (ell = 2, a = 1, k = 2): for large `m`, `R`, small `α₀`, EVERY `θ` is in class and has `GapAt` and the guarded inequality.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the guarded literal inequality at one twist configuration. -/
theorem InstIneqSG_twist (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hk : 1 ≤ k)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam) {a γ₀ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ₀) (θ : ℝ)
    (hQs : Function.Injective (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs)
    (hloc : InstIneqS selIn selIn ell k hell0 a Lu γ₀ S Lam (Uth (S.Om 0) 0)) :
    InstIneqSG selAll sJ ell k hell0 a Lu γ₀ S Lam (Uth (S.Om 0) θ) :=
  instIneqSG_of_gap selAll sJ ell k hell0 a Lu γ₀ S Lam (Uth (S.Om 0) θ)
    (GapAt_twist sJ hell0 hS hell hroom ha Lam θ hQs) (InstIneqSG2_twist sJ hell0 hk hS hell hroom hL ha hγ θ hloc)

#print axioms InstIneqSG_twist

/-- **the guarded literal headline restricted to the boundary-twist family** (thick tori, `Λ ≠ ∅`). -/
theorem SG_on_twist_family (sJ : PlaqSel) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
        ∀ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S →
        ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R k S Lam → Lam.Nonempty →
        ∀ θ : ℝ, ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Uth (S.Om 0) θ) →
          InstIneqSG selAll sJ ell k (by omega) a Lu γ₀ S Lam (Uth (S.Om 0) θ) := by
  have hell0 : 0 < ell := by omega
  obtain ⟨m₁, hm₁, hH1⟩ := Qs_injective_twist ell hell a ha
  obtain ⟨m₂, hm₂, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨max m₁ m₂, le_trans hm₁ (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨R₁, hR₁, hH2⟩ := hH1 m (le_trans (le_max_left _ _) hm)
  obtain ⟨R₂, hR₂⟩ := hmm m (le_trans (le_max_right _ _) hm)
  refine ⟨max R₁ R₂, fun R hR => ?_⟩
  obtain ⟨s, hs, hH⟩ := hH2 R (le_trans (le_max_left _ _) hR)
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₂ R (le_trans (le_max_right _ _) hR)
  refine ⟨min a₀ s, lt_min ha₀ hs, γ₀, hγ, fun k hk Lu α₀ hα hαle hT hthick S hS Lam hL hLne θ hU => ?_⟩
  have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := le_trans hαle (min_le_left _ _)
  have hαs : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s := le_trans hαle (min_le_right _ _)
  have hm1 : 1 ≤ m := le_trans hm₁ (le_trans (le_max_left _ _) hm)
  have hR18 : 18 ≤ R := le_trans hR₁ (le_trans (le_max_left _ _) hR)
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hQs := hH k hk Lu α₀ hα hαs hT S hS hthick Lam hL hLne θ hU selAll sJ
  have hflat : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Uth (S.Om 0) 0) := by
    refine ⟨hU.1, ?_⟩
    have := AdalyFormal.StatementLaneG.flat_perCubeRegular2cG ell (ell ^ m) 12 k hell0 (Nat.one_le_pow _ _ hell0) (by norm_num) hα S
    rw [Uth_zero]
    exact this
  have hloc := hcore k hk Lu α₀ hα hαa hT S hS Lam hL (Uth (S.Om 0) 0) hflat
  exact InstIneqSG_twist sJ hell0 hk hS hell hroom hL ha.le hγ θ hQs hloc

#print axioms SG_on_twist_family

end AdalyFormal.D1Guarded
