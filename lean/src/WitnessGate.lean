import WitnessReproduced
set_option autoImplicit false
namespace HConstruction.Nonflat
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open HConstruction.Nonflat.Reproduced

/-- Literal equality of the reproduced regularity predicate with the frozen one. -/
theorem regularity_exact (U : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (m : ℝ) :
    Reproduced.IsRegularHolonomy U m =
      AdalyFormal.Balaban.RegularityHolonomy.IsRegularHolonomy U m := rfl

/-- The exact admission threshold, not merely rejection at one test value. -/
theorem witness_regular_iff (m : ℝ) :
    AdalyFormal.Balaban.RegularityHolonomy.IsRegularHolonomy witnessU m ↔ 4 ≤ m := by
  change Reproduced.IsRegularHolonomy witnessU m ↔ 4 ≤ m
  constructor
  · intro h
    have hp := h witnessPlaquette
    rwa [holonomyDefectSq_witnessU_witnessPlaquette] at hp
  · intro h p
    exact (witnessU_isRegularHolonomy_four p).trans h

theorem witness_not_small {m : ℝ} (hm : m < 4) :
    ¬ AdalyFormal.Balaban.RegularityHolonomy.IsRegularHolonomy witnessU m := by
  rw [witness_regular_iff]
  exact not_le_of_gt hm

/-- The Frobenius convention is the existing certified smallness-bridge norm. -/
theorem witness_plaquette_frob :
    frobNorm ((holonomyElem witnessU witnessPlaquette : M2) - 1) = 2 := by
  rw [holonomy_witnessU_witnessPlaquette]
  norm_num [frobNorm, frobSq, witnessMElem, witnessM, Matrix.sub_apply, Matrix.one_apply]

/-- No global plaquette bound can use epsilon below two at this background. -/
theorem witness_plaquette_bound_requires_two (eps : ℝ)
    (h : ∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) witnessU p : M2) - 1) ≤ eps) :
    2 ≤ eps := by
  have hp := h witnessPlaquette
  change frobNorm ((holonomyElem witnessU witnessPlaquette : M2) - 1) ≤ eps at hp
  rwa [witness_plaquette_frob] at hp

/-- At ell=2 the certified cap bridge requires N*epsilon<2 with N=6.
This necessary input conjunction is impossible, before any jet estimate is used. -/
theorem witness_cap_bridge_impossible :
    ¬ ∃ eps : ℝ,
      (∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) witnessU p : M2) - 1) ≤ eps) ∧
      (6 : ℝ) * eps < 2 := by
  rintro ⟨eps, h, hs⟩
  have hb := witness_plaquette_bound_requires_two eps h
  linarith

/-- The uncapped bridge requires N*epsilon<sqrt 2, and fails as well. -/
theorem witness_bridge_impossible :
    ¬ ∃ eps : ℝ,
      (∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) witnessU p : M2) - 1) ≤ eps) ∧
      (6 : ℝ) * eps < Real.sqrt 2 := by
  rintro ⟨eps, h, hs⟩
  have hb := witness_plaquette_bound_requires_two eps h
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- Direct failure of the actual certified cap radius, not just of a sufficient
arithmetic condition for it. These radius definitions were byte-reproduced. -/
theorem witness_cap_radius_impossible :
    ¬ ∃ eps : ℝ,
      (∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) witnessU p : M2) - 1) ≤ eps) ∧
      Reproduced.loopRhoPlaqCap eps 2 < Real.pi / 2 := by
  rintro ⟨eps, h, hs⟩
  have hb := witness_plaquette_bound_requires_two eps h
  norm_num [Reproduced.loopRhoPlaqCap, Reproduced.loopSurfaceBound] at hs
  nlinarith [Real.pi_pos]

theorem witness_radius_impossible :
    ¬ ∃ eps : ℝ,
      (∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) witnessU p : M2) - 1) ≤ eps) ∧
      Reproduced.loopRhoPlaq eps 2 < Real.pi / 2 := by
  rintro ⟨eps, h, hs⟩
  have hb := witness_plaquette_bound_requires_two eps h
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hroot : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have hpi : Real.pi / (2 * Real.sqrt 2) > Real.pi / 4 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by positivity)
    linarith
  norm_num [Reproduced.loopRhoPlaq, Reproduced.loopSurfaceBound] at hs
  nlinarith [Real.pi_pos]

/-- Nonflat is not just nontrivial link data: curvature is genuinely nonzero. -/
theorem witness_not_covariant_complex :
    ¬ ∀ lam : PeriodicLatticeSite witnessL → SuTwo,
      curlValueCovariant witnessU (gradValueCovariant witnessU lam) = 0 := by
  intro h
  exact Reproduced.witness_curvature_ne_zero (congrFun (h witnessLam) witnessPlaquette)

/-- The source is the previously certified lossless i-chart source on H. -/
theorem witness_source_nonzero : HConstruction.Predicate.genuineSource witnessU ≠ 0 :=
  HConstruction.Predicate.genuineSource_witness_ne_zero

end HConstruction.Nonflat
