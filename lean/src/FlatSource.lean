import ProjectionSanity
set_option autoImplicit false
namespace HConstruction.Covariance
open HConstruction.Carrier HConstruction.Predicate
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- Polarization, used to identify a self-adjoint operator from its source form. -/
theorem selfAdjoint_zero_of_quadratic_zero (T : H →L[ℝ] H)
    (hs : ∀ x y, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (hq : ∀ x, (inner ℝ x (T x) : ℝ) = 0) : T = 0 := by
  ext x
  have hx : (inner ℝ (T x) (T x) : ℝ) = 0 := by
    have h := hq (x + T x)
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      hq x, hq (T x), ← hs] at h
    linarith
  exact (inner_self_eq_zero.mp hx)

/-- Every J-paired correction vanishes at the actual trivial source, regardless
of how its nonlinear coefficient is represented. This is not a chosen J. -/
theorem flat_source_pairing_zero (f : H → H) (A : H) :
    (inner ℝ (f A) (genuineSource (trivialU witnessL)) : ℝ) = 0 := by
  rw [show genuineSource (trivialU witnessL) = 0 from genuineSource_trivial,
    inner_zero_right]

/-- Both (3.120) and (3.134)/(3.135) are J-paired quadratic forms. Any
self-adjoint operator representing their sum is FORCED to vanish when U=1.
Hypotheses name form representation only; no physical G0/P is postulated. -/
theorem flat_source_form_forces_zero (T : H →L[ℝ] H)
    (hs : ∀ x y, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (f g : H → H)
    (hform : ∀ x, (inner ℝ x (T x) : ℝ) =
      inner ℝ (f x) (genuineSource (trivialU witnessL)) +
        2 * inner ℝ (g x) (genuineSource (trivialU witnessL))) : T = 0 := by
  apply selfAdjoint_zero_of_quadratic_zero T hs
  intro x
  rw [hform, flat_source_pairing_zero, flat_source_pairing_zero]
  norm_num

/-- Source-forced flat perturbation: NOT R, NOT the gauge-slice projection.
No concrete base covariance is claimed by this definition. -/
noncomputable def flatPerturbation : H →L[ℝ] H := 0

theorem flatPerturbation_converges (G0 : H →L[ℝ] H) :
    ‖flatPerturbation * G0‖ < 1 := by simp [flatPerturbation]

theorem flat_neumann_eq_base (G0 : H →L[ℝ] H) :
    Reproduced.gOneOfNeumann G0 flatPerturbation = G0 :=
  Reproduced.gOneOfNeumann_zero_perturbation G0

theorem flat_neumann_eq_tsum (G0 : H →L[ℝ] H) :
    Reproduced.gOneOfNeumann G0 flatPerturbation =
      ∑' n : ℕ, G0 * (flatPerturbation * G0) ^ n :=
  Reproduced.gOneOfNeumann_eq_tsum G0 flatPerturbation (flatPerturbation_converges G0)

theorem flatPerturbation_ne_gaugeSliceProjection :
    flatPerturbation ≠ gaugeSliceProjection := by
  exact Ne.symm gaugeSliceProjection_nonzero

/-- Full inverse covariance has to rule out the simultaneous kernel, not just
have a positive-semidefinite bare Delta. This iff fixes the precise remaining
finite-lattice obligation for the source-corrected construction. -/
theorem basePrecision_strict_iff (a : ℝ) (ha : 0 < a) :
    (∀ A : H, A ≠ 0 → (0 : ℝ) < inner ℝ A (basePrecision a A)) ↔
    (∀ A : H, flatCurl A = 0 → gaugeConstraint A = 0 →
      nativeLinearQ (trivialU witnessL) 2 A = 0 → A = 0) := by
  constructor
  · intro hp A hC hR hQ
    by_contra hn
    have h := hp A hn
    rw [basePrecision_energy, hC, hR, hQ] at h
    norm_num at h
  · intro hk A hn
    have hnonneg := basePrecision_nonneg a ha.le A
    by_contra hp
    have hz : (inner ℝ A (basePrecision a A) : ℝ) = 0 := le_antisymm (le_of_not_gt hp) hnonneg
    rw [basePrecision_energy] at hz
    have hC : ‖flatCurl A‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖flatCurl A‖, sq_nonneg ‖gaugeConstraint A‖,
        sq_nonneg ‖nativeLinearQ (trivialU witnessL) 2 A‖]
    have hR : ‖gaugeConstraint A‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖flatCurl A‖, sq_nonneg ‖gaugeConstraint A‖,
        sq_nonneg ‖nativeLinearQ (trivialU witnessL) 2 A‖]
    have hQ : ‖nativeLinearQ (trivialU witnessL) 2 A‖ ^ 2 = 0 := by
      nlinarith
    apply hn
    apply hk A
    · exact norm_eq_zero.mp (by nlinarith [norm_nonneg (flatCurl A)])
    · exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gaugeConstraint A)])
    · exact norm_eq_zero.mp (by nlinarith [norm_nonneg (nativeLinearQ (trivialU witnessL) 2 A)])

/-- The source Q really controls the constant field that made bare Delta singular. -/
theorem nativeLinearQ_constant_nonzero : nativeLinearQ (trivialU witnessL) 2 constantField ≠ 0 := by
  intro hz
  apply HConstruction.NonzeroJet.linearQ_A0_ne_zero
  have h := congrArg (fun X => ((cfl2Equiv 2 X HConstruction.NonzeroJet.c0 : SuTwo) :
    AdalyFormal.Balaban.SuTwoLogExp.M2)) hz
  have hc : fineCoordinates constantField = HConstruction.NonzeroJet.A0 := rfl
  simpa only [nativeLinearQ_exact, hc, map_zero, Pi.zero_apply, Submodule.coe_zero] using h

theorem basePrecision_constant_positive (a : ℝ) (ha : 0 < a) :
    (0 : ℝ) < inner ℝ constantField (basePrecision a constantField) := by
  rw [basePrecision_energy, flatCurl_constant]
  have hQ : 0 < ‖nativeLinearQ (trivialU witnessL) 2 constantField‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr nativeLinearQ_constant_nonzero)
  nlinarith [sq_nonneg ‖gaugeConstraint constantField‖]

end HConstruction.Covariance
