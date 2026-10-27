/-! Cofinal equivalents of the full-kernel criterion. No instance of the
noncancellation condition is asserted. Known round-9 regularity is explicit. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R4
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Assembly.R3 (RegularityFacts)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- The geometric response has no additional scalar-detection obstruction. -/
theorem responseGradient_ne_zero_iff (q R : ℕ) (u : TwistSpace q R) :
    responseGradient q R u ≠ 0 ↔ CurlDetected q R u := by
  rw [← exists_profile_iff_curlDetected]
  constructor
  · intro h
    refine ⟨fun b => responseGradient q R u b, ?_⟩
    rw [profileCoupling_gradient]
    exact ne_of_gt (real_inner_self_pos.mpr h)
  · rintro ⟨f, hf⟩ hz
    apply hf
    rw [profileCoupling_gradient, hz, inner_zero_right]

/-- Necessary detection on every nonzero vector of the complete crossing kernel. -/
theorem curlDetected_of_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (h : NoResponseCancellation q R V) (u : TwistSpace q R)
    (hu : vacA q R V 1 (vacEdge q R V) u = 0) (hne : u ≠ 0) :
    CurlDetected q R u :=
  (responseGradient_ne_zero_iff q R u).mp
    (responseGradient_ne_zero_of_noCancellation q R V h u hu hne)

def CofinalNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      NoResponseCancellation (2^j) R (uthPath (2^j) R)

def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V

theorem cofinalAnyProfileCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyProfileCoupling ↔ CofinalNoResponseCancellation := by
  constructor
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hf⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R (uthPath _ _)
        (hr (2^j) R (by positivity) hR hR18)).mp hf⟩
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hnc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R (uthPath _ _)
        (hr (2^j) R (by positivity) hR hR18)).mpr hnc⟩

theorem cofinalAnyPathCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation := by
  constructor
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, hf⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R V
        (hr (2^j) R (by positivity) hR hR18)).mp hf⟩
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, hnc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R V
        (hr (2^j) R (by positivity) hR hR18)).mpr hnc⟩

theorem cofinalNoCancellation_of_curlLine (hr : RegularityFacts)
    (h : R3.CofinalCurlLine) : CofinalNoResponseCancellation :=
  (cofinalAnyProfileCoupling_iff_noCancellation hr).mp
    (R3.cofinalAnyProfileCoupling_of_curlLine hr h)

theorem cofinalAnyPathNoCancellation_of_curlLine (hr : RegularityFacts)
    (h : R3.CofinalAnyPathCurlLine) : CofinalAnyPathNoResponseCancellation :=
  (cofinalAnyPathCoupling_iff_noCancellation hr).mp
    (R3.cofinalAnyPathCoupling_of_curlLine hr h)

#print axioms responseGradient_ne_zero_iff
#print axioms curlDetected_of_noCancellation
#print axioms CofinalNoResponseCancellation
#print axioms CofinalAnyPathNoResponseCancellation
#print axioms cofinalAnyProfileCoupling_iff_noCancellation
#print axioms cofinalAnyPathCoupling_iff_noCancellation
#print axioms cofinalNoCancellation_of_curlLine
#print axioms cofinalAnyPathNoCancellation_of_curlLine
end AdalyFormal.Round10.Assembly.R4
