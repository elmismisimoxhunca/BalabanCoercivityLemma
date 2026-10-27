import FlatOperators
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace HConstruction.Covariance
open HConstruction.Carrier HConstruction.Predicate
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY blockOf)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.KernelSubspace (kernelWitnessSiteA kernelWitnessSiteB)

/-- Two different sites in the same genuine block: the source R is NOT zero. -/
noncomputable def siteTest : S := (fiberEquiv _).symm (fun x =>
  (if x = kernelWitnessSiteA then suTwoWitness else 0) -
  (if x = kernelWitnessSiteB then suTwoWitness else 0))

lemma same_block_membership : ∀ y :
    {y : PeriodicLatticeSite witnessL // y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 2},
    (kernelWitnessSiteA ∈ blockOf y.1 2 ↔ kernelWitnessSiteB ∈ blockOf y.1 2) := by
  decide

lemma siteTest_mem_kernel : siteTest ∈ LinearMap.ker flatSiteQ := by
  rw [LinearMap.mem_ker]
  funext y
  change coarseRestrictSiteCovariant 2
    (fun x => (if x = kernelWitnessSiteA then suTwoWitness else 0) -
      (if x = kernelWitnessSiteB then suTwoWitness else 0)) y.1 = 0
  simp only [coarseRestrictSiteCovariant, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp [same_block_membership y]

lemma flatGrad_siteTest_ne_zero : flatGrad siteTest ≠ 0 := by
  intro hz
  have h := congrArg (fun A : H => bfl2Equiv A (witnessY, 0)) hz
  have ha : periodicLatticeShift witnessY 0 = kernelWitnessSiteA := by decide
  have hab : kernelWitnessSiteA ≠ kernelWitnessSiteB := by decide
  have hya : witnessY ≠ kernelWitnessSiteA := by decide
  have hyb : witnessY ≠ kernelWitnessSiteB := by decide
  have hv : (2 : ℝ) • suTwoWitness = 0 := by
    simpa [flatGrad, siteTest, gradCovariantLM, gradValueCovariant, trivialU,
      RMap_one, ha, hab, hya, hyb] using h
  exact suTwoWitness_ne_zero ((smul_eq_zero.mp hv).resolve_left (by norm_num))

lemma flatSiteDelta_siteTest_ne_zero : flatSiteDelta siteTest ≠ 0 := by
  intro hz
  have h := congrArg (fun x : S => (inner ℝ siteTest x : ℝ)) hz
  have hn : ‖flatGrad siteTest‖ ^ 2 = 0 := by
    simpa only [flatSiteDelta, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      inner_zero_right] using h
  exact flatGrad_siteTest_ne_zero (norm_eq_zero.mp (by nlinarith [norm_nonneg (flatGrad siteTest)]))

theorem siteR_nonzero : siteR ≠ 0 := by
  intro hz
  have hm : flatSiteDelta siteTest ∈ gaugeImage :=
    ⟨siteTest, siteTest_mem_kernel, rfl⟩
  have hfix : siteR (flatSiteDelta siteTest) = flatSiteDelta siteTest :=
    Submodule.starProjection_eq_self_iff.mpr hm
  rw [hz, zero_apply] at hfix
  exact flatSiteDelta_siteTest_ne_zero hfix.symm

/-- The orthogonal projection onto the H-valued gauge slice exists, but it is
NOT the perturbation argument of (3.138). -/
noncomputable def gaugeSliceProjection : H →L[ℝ] H :=
  (LinearMap.ker gaugeConstraint.toLinearMap).starProjection

theorem gaugeSliceProjection_idempotent :
    gaugeSliceProjection * gaugeSliceProjection = gaugeSliceProjection :=
  Submodule.isIdempotentElem_starProjection _

theorem gaugeConstraint_not_injective : ¬ Function.Injective gaugeConstraint := by
  intro hinj
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := gaugeConstraint.toLinearMap) hinj
  have hH : Module.finrank ℝ H = 192 * Module.finrank ℝ SuTwo := by
    rw [bfl2Equiv.finrank_eq, Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, witness_bond_counts.1]
  have hS : Module.finrank ℝ S = 64 * Module.finrank ℝ SuTwo := by
    rw [(fiberEquiv (PeriodicLatticeSite witnessL)).finrank_eq, Module.finrank_pi_fintype]
    have hc : Fintype.card (PeriodicLatticeSite witnessL) = 64 := by decide
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]
  rw [hH, hS] at hdim
  have hp : 0 < Module.finrank ℝ SuTwo := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨suTwoWitness, suTwoWitness_ne_zero⟩
  omega

theorem gaugeSliceProjection_nonzero : gaugeSliceProjection ≠ 0 := by
  intro hz
  apply gaugeConstraint_not_injective
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have h : gaugeSliceProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  rw [hz, zero_apply] at h
  exact h.symm

/-- Algebraic sanity: a nonzero perturbation cannot preserve an invertible base
covariance when the reproduced Neumann series converges. -/
theorem neumann_eq_base_iff (G0 G0inv P : H →L[ℝ] H)
    (hi : G0inv * G0 = 1) (hir : G0 * G0inv = 1) (hc : ‖P * G0‖ < 1) :
    Reproduced.gOneOfNeumann G0 P = G0 ↔ P = 0 := by
  constructor
  · intro h
    have he := Reproduced.gOneOfNeumann_cancel_right G0 P hc
    rw [h] at he
    have he' := congrArg (fun T : H →L[ℝ] H => G0inv * T) he
    rw [← mul_assoc, hi, one_mul] at he'
    have hp0 : P * G0 = 0 := by
      have ht : 1 - P * G0 = 1 := he'
      exact sub_eq_self.mp ht
    have hp := congrArg (fun T : H →L[ℝ] H => T * G0inv) hp0
    simpa only [mul_assoc, hir, mul_one, zero_mul] using hp
  · intro hp
    rw [hp]
    exact Reproduced.gOneOfNeumann_zero_perturbation G0

/-- The literal projection proposal in the task fails the flat-source G1=G0 test.
Not a claim that any G0 in this statement has been physically constructed. -/
theorem gauge_slice_is_not_flat_neumann_perturbation
    (G0 G0inv : H →L[ℝ] H) (hi : G0inv * G0 = 1) (hir : G0 * G0inv = 1)
    (hc : ‖gaugeSliceProjection * G0‖ < 1) :
    Reproduced.gOneOfNeumann G0 gaugeSliceProjection ≠ G0 := by
  intro h
  exact gaugeSliceProjection_nonzero ((neumann_eq_base_iff G0 G0inv _ hi hir hc).mp h)

end HConstruction.Covariance
