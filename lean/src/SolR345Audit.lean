import GdR5b
import GdSG5
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace SolR345Audit
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal AdalyFormal.D1Guarded AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

-- Independently state the omitted-sector characterization against the actual predicates.
theorem no_testfield_iff_zero (ell : ℕ) (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu)) :
    (¬ ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) ↔
    (∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt → Bt = 0) := by
  constructor
  · intro h Bt h1 h2
    apply bondEnergy_eq_zero
    apply le_antisymm _ (bondEnergy_nonneg Bt)
    by_contra hn
    exact h ⟨Bt, h1, h2, lt_of_not_ge hn⟩
  · intro h ⟨Bt, h1, h2, hE⟩
    rw [h Bt h1 h2] at hE
    have hzero : bondEnergy (0 : Bond Lu → SuTwo) = 0 := by
      unfold bondEnergy
      exact Finset.sum_eq_zero (fun b _ => by simp)
    rw [hzero] at hE
    exact (lt_irrefl 0) hE

-- Interface pin to the real headline: no surrogate residual or operator is used.
theorem no_separating_instance :
    ¬ ((P428Target8SG selAll selAll ∧ ¬ GuardResidualT selAll selAll) ∨
       (GuardResidualT selAll selAll ∧ ¬ P428Target8SG selAll selAll)) := by
  have h := P428Target8SG_iff_residualT selAll selAll
    (fun _ _ => Set.subset_univ _) (fun _ _ => Set.subset_univ _)
  rintro (⟨hs, hn⟩ | ⟨hr, hn⟩)
  · exact hn (h.mp hs)
  · exact hn (h.mpr hr)

-- Nonzero test-field diagnostic on the very same NV geometry; fresh assertion,
-- proof adapted from the permitted prior Sol witness, not an independent construction.
noncomputable def checkedSeed (m R : ℕ) (hM : 0 < 2^m) : Bond (nvLu (2^m) R) → SuTwo :=
  BseedNv 2 hM

theorem seed_energy (m R : ℕ) (hm : 1 ≤ m) :
    0 < bondEnergy (checkedSeed m R (pow_pos (by norm_num) m)) := by
  have hM : 0 < 2^m := pow_pos (by norm_num) m
  have hdvd : 2 ∣ 2^m := dvd_pow_self 2 (by omega)
  exact (BseedNv_props (R := R) (show 2 ≤ 2 by omega) hdvd hM).2.2.1

-- Test the lower-unit input of the openness argument with a scalar specialization.
noncomputable def checkedOp : ℝ →L[ℝ] ℝ := 1

theorem domination_unit : IsUnit checkedOp := by
  apply isUnit_of_psd_ge (M₂ := (1 : ℝ →L[ℝ] ℝ))
  · intro x y; simp
  · intro x; simp only [ContinuousLinearMap.one_apply]; exact real_inner_self_nonneg
  · exact isUnit_one
  · intro x
    change ⟪x, x⟫ ≤ ⟪x, checkedOp x⟫
    simp [checkedOp]

-- One-shot push of the general-U result to the full-guard headline.
-- This packages the exhibit's proved pointwise theorem; it is not a proof of SG.
theorem full_guard_literal : P428Target8SG2 selAll selAll := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hmm m hm
  refine ⟨max R₀ 18, fun R hR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ R (le_trans (le_max_left _ _) hR)
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU => ?_⟩
  have hell0 : 0 < ell := by omega
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 (le_trans hm₀ hm)
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  exact InstIneqSG2_general selAll selAll hell0 hS hk hroom ha.le hγ Lam U
    (fun _ _ => Set.subset_univ _) (fun _ _ => Set.subset_univ _)
    (hcore k hk Lu α₀ hα hαle hT S hS Lam hL U hU)

#print axioms full_guard_literal
#print axioms no_testfield_iff_zero
#print axioms no_separating_instance
#print axioms seed_energy
#print axioms domination_unit
end SolR345Audit

#print axioms AdalyFormal.D1Guarded.isUnit_Q_inv_Qs_of_pos_ker
#print axioms AdalyFormal.D1Guarded.Qs_injective_twist
#print axioms AdalyFormal.D1Guarded.Gp_Rproj_mem_NQp
#print axioms AdalyFormal.D1Guarded.Fth_theta_apply_eq
#print axioms AdalyFormal.D1Guarded.GapAt_twist
#print axioms AdalyFormal.D1Guarded.InstIneqSG2_twist
#print axioms AdalyFormal.D1Guarded.SG_on_twist_family_nv
#print axioms AdalyFormal.D1Guarded.genFormS_eq_loc
#print axioms AdalyFormal.D1Guarded.NG_unit_of_N1
#print axioms AdalyFormal.D1Guarded.InstIneqSG2_general
#print axioms AdalyFormal.D1Guarded.InstIneqS_of_no_testfield
#print axioms AdalyFormal.D1Guarded.GuardResidualT
#print axioms AdalyFormal.D1Guarded.P428Target8SG_of_residualT
#print axioms AdalyFormal.D1Guarded.residualT_of_P428Target8SG
#print axioms AdalyFormal.D1Guarded.P428Target8SG_iff_residualT
#print axioms AdalyFormal.D1Guarded.Fth_zero_isUnit
#print axioms AdalyFormal.D1Guarded.Fth_isUnit_near_zero
#print axioms AdalyFormal.D1Guarded.nv_guard_nonvacuous
#print axioms AdalyFormal.M2RightInv.p428Target8
