import NsPtC

/-!
# PtD1 -- at a flat background the `Ginv` form vanishing means curl-free on `plaqIn Om0`, `T x = 0` and `Q x = 0` (any tower geometry) (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

/-- the flat `Ginv` form is the sum of three nonnegative terms. -/
theorem flat_ginv_form (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, P.data.Ginv x⟫ =
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, P.data.Dpi x⟫ = ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, P.data.Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, P.data.Mass x⟫ = ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, P.data.Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

theorem flat_ginv_zero (P : IngrBParams) (hU : P.U = flatCfg) (ha : 0 < P.a) (x : ↥(bondSupp P.G))
    (h0 : ⟪x, P.data.Ginv x⟫ = 0) :
    AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) P.Lf) (iE P.G x)) = 0
      ∧ Tfull P.G P.U (iE P.G x) = 0 ∧ P.sector.Qfull (iE P.G x) = 0 := by
  rw [flat_ginv_form P hU x] at h0
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
  have t1 := sq_nonneg ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · have : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · have hs : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by positivity)).mp hs
    refine PiLp.ext (fun p => ?_)
    have h1 := hz p (Finset.mem_univ p)
    have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by positivity
    have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hp.ne'
      · exact h
    have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    simpa using this

#print axioms flat_ginv_zero

end AdalyFormal.CoverOmega
