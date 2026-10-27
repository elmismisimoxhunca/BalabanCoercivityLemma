import SourcePredicate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
Upgrade the already-certified SI1 identity-log argument from one-dimensional
first derivatives to smooth germs on arbitrary real normed spaces. The true
principal log is retained, including its removable closed-form singularity at 1.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HConstruction.LocalLog
open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Log su2Exp su2Kappa su2Angle su2NegOne coe_one
   su2Log_antiHermitian su2Log_traceless su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.RegularityGap (Yof su2_exp_log_of_ne_negOne)
open AdalyFormal.Balaban.Bch2 (kappa_nonneg kappa_le)
open AdalySI1.RawUbarDerivNoLoop
  (Yof_eq_ambient continuous_yofAmbient su2Log_eq_kappa_rsmul su2Angle_le_pi_div_two_iff)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- SI1's identity-log continuity argument, with arbitrary parameter space. -/
theorem tendsto_log_zero {V : E → SU2} {x : E}
    (hG : ContinuousAt (fun t => ((V t : SU2) : M2)) x) (hval : V x = 1) :
    Filter.Tendsto (fun t => su2Log (V t)) (nhds x) (nhds (0 : M2)) := by
  have hVtend := hG.tendsto
  simp only [hval, coe_one] at hVtend
  have htrace_tend : Filter.Tendsto (fun t => (Matrix.trace ((V t : SU2) : M2)).re)
      (nhds x) (nhds 2) := by
    have hcont : Continuous (fun Z : M2 => (Matrix.trace Z).re) := by
      have hlin : Continuous (fun Z : M2 => Matrix.trace Z) :=
        (Matrix.traceLinearMap (Fin 2) ℂ ℂ).continuous_of_finiteDimensional
      fun_prop
    have h := (hcont.continuousAt (x := (1 : M2))).tendsto.comp hVtend
    have h3 : (Matrix.trace (1 : M2)).re = 2 := by simp
    rwa [h3] at h
  have hangle_le : ∀ᶠ t in nhds x, su2Angle (V t) ≤ Real.pi / 2 := by
    have hpos := htrace_tend.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hpos] with t ht
    exact (su2Angle_le_pi_div_two_iff (V t)).2 (le_of_lt ht)
  have hYof_tend : Filter.Tendsto (fun t => Yof (V t)) (nhds x) (nhds (0 : M2)) := by
    have h := (continuous_yofAmbient.continuousAt (x := (1 : M2))).tendsto.comp hVtend
    have heq : (fun t => Yof (V t)) = (fun t => ((V t : SU2) : M2) -
        (((Matrix.trace ((V t : SU2) : M2)).re / 2 : ℝ) : ℂ) • (1 : M2)) := by
      funext t; exact Yof_eq_ambient _
    rw [heq]
    have h3 : (1 : M2) - (((Matrix.trace (1 : M2)).re / 2 : ℝ) : ℂ) • (1 : M2) = (0 : M2) := by
      have h4 : (Matrix.trace (1 : M2)).re = 2 := by simp
      rw [h4]; norm_num
    rw [h3] at h
    exact h
  have hbound : ∀ᶠ t in nhds x, ‖su2Log (V t)‖ ≤ (Real.pi / 2) * ‖Yof (V t)‖ := by
    filter_upwards [hangle_le] with t ht
    rw [su2Log_eq_kappa_rsmul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (kappa_nonneg (V t))]
    exact mul_le_mul_of_nonneg_right (kappa_le ht) (norm_nonneg _)
  have hRHS_tend : Filter.Tendsto (fun t => (Real.pi / 2) * ‖Yof (V t)‖)
      (nhds x) (nhds 0) := by
    have h := (continuous_norm.continuousAt (x := (0 : M2))).tendsto.comp hYof_tend
    simp only [norm_zero] at h
    simpa using h.const_mul (Real.pi / 2)
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS_tend
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hbound)

/-- Genuine smoothness at identity, not smoothness of a replacement logarithm. -/
theorem contDiffAt_log_at_one {V : E → SU2} {x : E}
    (hG : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x) (hval : V x = 1) :
    ContDiffAt ℝ ⊤ (fun t => su2Log (V t)) x := by
  have hexp : ContDiffAt ℝ ⊤ (NormedSpace.exp : M2 → M2) (0 : M2) :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) 0).contDiffAt
  have hfd : HasFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 →L[ℝ] M2)) (0 : M2) := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero.hasFDerivAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let hstrict := hexp.hasStrictFDerivAt' hfd hn
  let Φ := hstrict.toOpenPartialHomeomorph NormedSpace.exp
  let g0 := hexp.localInverse hfd hn
  have hg0 : ContDiffAt ℝ ⊤ g0 (1 : M2) := by
    simpa only [NormedSpace.exp_zero] using hexp.to_localInverse hfd hn
  have hsrc_nhds : Φ.source ∈ nhds (0 : M2) :=
    Φ.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have htgt_nhds : Φ.target ∈ nhds (1 : M2) := by
    rw [← (NormedSpace.exp_zero : NormedSpace.exp (0 : M2) = (1 : M2))]
    exact Φ.open_target.mem_nhds hstrict.image_mem_toOpenPartialHomeomorph_target
  have hVtend := hG.continuousAt.tendsto
  simp only [hval, coe_one] at hVtend
  have hev_source := (tendsto_log_zero hG.continuousAt hval).eventually hsrc_nhds
  have hev_target := hVtend.eventually htgt_nhds
  have hneM : (1 : M2) ≠ ((su2NegOne : SU2) : M2) := by
    intro h
    exact AdalyFormal.Balaban.SuTwoLogExp.su2NegOne_ne_one (Subtype.ext h.symm)
  have hev_ne := hVtend.eventually (eventually_ne_nhds hneM)
  have heq_ev : (fun t => g0 ((V t : SU2) : M2)) =ᶠ[nhds x] (fun t => su2Log (V t)) := by
    filter_upwards [hev_source, hev_target, hev_ne] with t hsrc htgt hne
    have hcut : V t ≠ su2NegOne := fun h => hne (congrArg Subtype.val h)
    have hexp1 : NormedSpace.exp (su2Log (V t)) = ((V t : SU2) : M2) := by
      rw [← su2Exp_coe_of_antiHerm_traceless (su2Log_antiHermitian (V t))
        (su2Log_traceless (V t)), su2_exp_log_of_ne_negOne (V t) hcut]
    exact Φ.injOn (Φ.map_target htgt) hsrc ((Φ.right_inv htgt).trans hexp1.symm)
  have hval' : ((V x : SU2) : M2) = (1 : M2) := by rw [hval]; exact coe_one
  rw [← hval'] at hg0
  exact (hg0.comp x hG).congr_of_eventuallyEq heq_ev.symm

end HConstruction.LocalLog

run_cmd do
  for name in [`HConstruction.LocalLog.tendsto_log_zero,
      `HConstruction.LocalLog.contDiffAt_log_at_one] do
    let ax ← Lean.collectAxioms name
    for a in ax do
      unless ([`propext, `Classical.choice, `Quot.sound] : List Lean.Name).contains a do
        throwError "Nonstandard local log axiom {name}: {a}"
    Lean.logInfo m!"LOCAL_LOG_AXIOMS {name}: {ax}"
