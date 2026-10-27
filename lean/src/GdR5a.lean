import GdGen9

/-!
# GdR5a -- the TIGHT residual `GuardResidualT` and the equivalence
`P428Target8SG sD sJ  <->  GuardResidualT sD sJ` (selectors containing `plaqIn Ω₀`).

`GuardResidualT` is quantified exactly as the headline consumes it: `ell ≥ 2`, `a > 0`, `M = ell^m`, `m ≥ m₀`, `R ≥ R₀`, `0 < α₀`, `12 M α₀ ≤ a₀`, `k ≥ 1`,
`TorusOK`, `Admissible`, `LambdaOK2`, `ClassCoupled`; one positive-energy admissible test field is assumed to exist.  Its thresholds `m₀, R₀, a₀` are existential
(the same shape as the headline's).  The localised headline is proved, so the guarded literal headline is equivalent to this single statement.
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
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

/-- without a positive-energy admissible test field the literal inequality is trivial. -/
theorem InstIneqS_of_no_testfield (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {a γ₀ : ℝ} (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hno : ¬ ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) :
    InstIneqS sD sJ ell k hell0 a Lu γ₀ S Lam U := by
  intro Bt h1 h2
  have hE : bondEnergy Bt ≤ 0 := by
    by_contra hpos
    push Not at hpos
    exact hno ⟨Bt, h1, h2, hpos⟩
  have hBt : Bt = 0 := bondEnergy_eq_zero (le_antisymm hE (bondEnergy_nonneg Bt))
  subst hBt
  have hE0 : bondEnergy (0 : Bond Lu → SuTwo) = 0 := by
    unfold bondEnergy
    exact Finset.sum_eq_zero (fun b _ => by simp)
  rw [hE0, mul_zero]
  have hB0' : (WithLp.toLp 2 ((GenP.genC (gparams ell k Lu hell0 S U a Lam)) 0) :
      BondFnL2 (gparams ell k Lu hell0 S U a Lam).Lu) = 0 := by
    rw [map_zero]; rfl
  exact ((congrArg (GenS.genFormS sD sJ (gparams ell k Lu hell0 S U a Lam)) hB0').trans
    (genFormS_zero sD sJ (gparams ell k Lu hell0 S U a Lam))).ge

/-- **the tight residual**, quantified as the headline consumes it. -/
def GuardResidualT (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
        IsUnit (dataS sD sJ (gparams ell k Lu (by omega) S U a Lam)).Ginv →
        IsUnit (G1invS sD sJ (gparams ell k Lu (by omega) S U a Lam))

theorem P428Target8SG_of_residualT (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hres : GuardResidualT sD sJ) : P428Target8SG sD sJ := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, hres1⟩ := hres ell hell a ha
  obtain ⟨m₂, hm₂, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨max m₁ m₂, le_trans hm₁ (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨R₁, hres2⟩ := hres1 m (le_trans (le_max_left _ _) hm)
  obtain ⟨R₂, hR₂⟩ := hmm m (le_trans (le_max_right _ _) hm)
  refine ⟨max (max R₁ R₂) 18, fun R hR => ?_⟩
  have hRa : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a₁, ha₁, hres3⟩ := hres2 R hRa
  obtain ⟨hside, a₂, ha₂, γ₀, hγ, hcore⟩ := hR₂ R hRb
  refine ⟨hside, min a₁ a₂, lt_min ha₁ ha₂, γ₀, hγ, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU => ?_⟩
  have hell0 : 0 < ell := by omega
  have hm1 : 1 ≤ m := le_trans hm₁ (le_trans (le_max_left _ _) hm)
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁ := le_trans hαle (min_le_left _ _)
  have hαb : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₂ := le_trans hαle (min_le_right _ _)
  have hloc := hcore k hk Lu α₀ hα hαb hT S hS Lam hL U hU
  by_cases hex : ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt
  · obtain ⟨Bt, h1, h2, hE⟩ := hex
    have hWD2 := WellDefAt_loc_of_inst ell k hell0 a ha.le Lu γ₀ hγ S Lam U Bt h1 h2 hE hloc
    exact InstIneqSG_general sD sJ hell0 hS hk hroom ha.le hγ Lam U hsD hsJ hloc hWD2
      (hres3 k hk Lu α₀ hα hαa hT S hS Lam hL U hU ⟨Bt, h1, h2, hE⟩)
  · intro _
    exact InstIneqS_of_no_testfield sD sJ hell0 Lam U hex

/-- **the converse**: the guarded literal headline implies the tight residual. -/
theorem residualT_of_P428Target8SG (sD sJ : PlaqSel) (h : P428Target8SG sD sJ) : GuardResidualT sD sJ := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hR
  refine ⟨a₀, ha₀, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU ⟨Bt, h1, h2, hE⟩ hu => ?_⟩
  have hI := hc k hk Lu α₀ hα hαle hT S hS Lam hL U hU
  exact (gap_of_instIneqSG sD sJ ell k (by omega) a ha.le Lu γ₀ hγ S Lam U Bt h1 h2 hE hI hu).1

/-- **equivalence**: the guarded literal headline is equivalent to the tight residual (the localised headline being a theorem). -/
theorem P428Target8SG_iff_residualT (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G) :
    P428Target8SG sD sJ ↔ GuardResidualT sD sJ :=
  ⟨residualT_of_P428Target8SG sD sJ, P428Target8SG_of_residualT sD sJ hsD hsJ⟩

#print axioms InstIneqS_of_no_testfield
#print axioms P428Target8SG_of_residualT
#print axioms residualT_of_P428Target8SG
#print axioms P428Target8SG_iff_residualT

end AdalyFormal.D1Guarded
