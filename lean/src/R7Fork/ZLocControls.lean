import ZLocOps
import R7Fork.AdalyFormal.Balaban.CoercivityRegular

/-!
# ZLocControls -- the localisation is NOT vacuous (r6 R1 must-fire control, content-bearing)
At the flat background on the tree's `witnessL` torus the r5 (global-plaquette-sum) `Δ` has quadratic form `4` on the spike
`deltaWitnessConfig`, while the Dirichlet-localised `Δ` with `Ω₀ = ∅` (no plaquette of `Ω₀`) has form `0`:
`deltaKLocCLM U ∅ = 0` (theorem `deltaKLocCLM_empty`).  A mutant that restores the global plaquette sum makes the second
equality false.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR6

open scoped RealInnerProductSpace
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaPrime (deltaWitnessConfig)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem plaqMask_empty {L : PeriodicLatticeExtent} (f : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L) :
    plaqMask (∅ : Set (PeriodicLatticePlaquette L)) f = 0 := by
  refine PiLp.ext (fun p => ?_)
  simp [plaqMask_apply]

theorem deltaPrimeBilL2NormLoc_empty {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U (∅ : Set (PeriodicLatticePlaquette L)) x y = 0 := by
  show deltaPrimeBilNormLoc U ∅ _ _ = 0
  unfold deltaPrimeBilNormLoc
  have h : deltaPrimeBilRawLoc U (∅ : Set (PeriodicLatticePlaquette L)) = 0 := by
    unfold deltaPrimeBilRawLoc
    simp
  rw [h]
  simp

/-- with no plaquette in `P`, `Δ_loc = 0` (Dirichlet: nothing inside). -/
theorem deltaKLocCLM_empty {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaKLocCLM U (∅ : Set (PeriodicLatticePlaquette L)) = 0 := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [inner_deltaKLocCLM, plaqMask_empty, plaqMask_empty, deltaPrimeBilL2NormLoc_empty]
  simp

/-- the r5 (global) `Δ` at the flat background on the spike: form `4`. -/
theorem global_spike_form :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      (deltaKCLMNormalized (trivialU witnessL) (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = 4 := by
  rw [inner_deltaKCLMNormalized_eq]
  rw [AdalyFormal.Balaban.CoercivityRegular.deltaKQuadFormNormalizedCorrected_eq_sub]
  have h0 : AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm (trivialU witnessL) deltaWitnessConfig = 0 :=
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm_vanishes_at_trivial _
  rw [h0]
  have h4 : AdalyFormal.Balaban.CovariantHj.dstarDQuadForm (trivialU witnessL) deltaWitnessConfig = 4 := by
    show AdalyFormal.Balaban.CovariantHj.dstarDQuadForm (trivialU witnessL)
      (AdalyFormal.Balaban.CoercivityRegular.spikeWitness (witnessY, (0 : Fin 3))) = 4
    rw [AdalyFormal.Balaban.CoercivityRegular.spike_dstarDQuadForm_indep (trivialU witnessL)
      AdalyFormal.Balaban.CovariantOperators.witnessU (witnessY, (0 : Fin 3))
      (by decide : ∀ μ : Fin 3, 0 < witnessL μ)]
    exact AdalyFormal.Balaban.NormalizationAudit.dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four
  rw [h4]; ring

/-- **CONTROL (non-forced): the localisation changes the operator.**  Global `Δ` has form `4` on the spike at the flat
background; `Δ_loc` with no plaquette in `P` has form `0`. -/
theorem global_ne_localised_empty :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      (deltaKCLMNormalized (trivialU witnessL) (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) ≠
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      (deltaKLocCLM (trivialU witnessL) (∅ : Set (PeriodicLatticePlaquette witnessL))
        (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) := by
  rw [global_spike_form, deltaKLocCLM_empty]
  simp

#print axioms deltaKLocCLM_empty
#print axioms global_spike_form
#print axioms global_ne_localised_empty

end AdalyFormal.StatementLaneR6
