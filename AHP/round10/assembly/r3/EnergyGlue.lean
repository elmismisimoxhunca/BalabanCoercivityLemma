/-! Exact derivative/explicit-form glue and free-path cofinal bookkeeping.
ProfileRegular packages only the three regularity facts already compiled in round 9.
The final historical application of those facts is kept separate from this compact harness. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace Topology
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource (profileCoupling CurlDetected)
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- The explicit R3 profile agrees definitionally with the dictionary's physical profile. -/
theorem responseProfile_eq (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R u = Dictionary.FreeSource.responseProfile q R u := rfl

/-- Fixed carrier types avoid dependent elaboration through the varying background. -/
abbrev profileData (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    BaseDataS (TwistSpace q R) (SiteL2 (scaleUp 2 1 (dilLu q R)))
      (FSp (geomOf 2 1 (dilTower q R))) := dataS selIn selIn (bulkP q R f ε)

/-- Already-proved round-9 inputs, retained visibly instead of using uncompiled stand-ins. -/
def ProfileRegular (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ContinuousAt (fun ε : ℝ => (profileData q R f ε).H) 0 ∧
  (∀ u : TwistSpace q R, Tendsto (fun ε : ℝ => (profileData q R f ε).C2 u)
    (𝓝 0) (𝓝 ((profileData q R f 0).C2 u))) ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f) 0

def RegularityFacts : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f

/-- Source vanishing proves flat correction vanishing without any radius assumptions. -/
theorem bulkD_zero_source (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    bulkD q R f 0 = 0 := by
  have hs := (profileData q R f 0).Delta2_spec (dataS_laws selIn selIn _)
  apply symm_unique hs.1
    (S2 := (0 : TwistSpace q R →L[ℝ] TwistSpace q R))
    (fun x y => by simp only [zero_apply, inner_zero_left, inner_zero_right])
  intro u
  rw [hs.2 u, bulkSource_zero]
  change 2 * ⟪(profileData q R f 0).H ((profileData q R f 0).C2 u),
    (0 : TwistSpace q R)⟫ = ⟪u, (0 : TwistSpace q R)⟫
  rw [inner_zero_right, inner_zero_right, mul_zero]

theorem bulkData_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    dataS selIn selIn (bulkP q R f 0) = flatData q R := by
  have hu : bulkU q R f 0 = (fun _ => 1) := by
    rw [bulkU_phase]
    funext b
    simp only [Dictionary.PhaseSource.phase, zero_mul, Dictionary.PhaseSource.phase_zero]
  unfold bulkP
  rw [hu]

/-- Exact actual derivative identification for an arbitrary profile, using only
round-9 regularity and the unconditional R2 source stencil limit. -/
theorem corrDeriv_profile_form (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hr : ProfileRegular q R f)
    (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u := by
  have ht := Dictionary.PhaseSource.tendsto_div_of_hasDerivAt_zero
    (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f)
    (bulkD_zero_source q R f) hr.2.2
  have h := limit_Delta2_div_form
    (profileData q R f) (fun _ => dataS_laws selIn selIn _) 
    hr.1 hr.2.1 (profileSourceStencil q R f) (bulkSource_tendsto q R f)
    (corrDeriv q R f)
    (ht.mono_left (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))) u
  change ⟪u, corrDeriv q R f u⟫ =
    2 * ⟪(dataS selIn selIn (bulkP q R f 0)).H
      ((dataS selIn selIn (bulkP q R f 0)).C2 u), profileSourceStencil q R f⟫ at h
  rw [bulkData_zero] at h
  exact h

/-- The whole kernel is essential; the adaptive profile is chosen from its generator. -/
theorem canonicalCoupling_of_curlDetected {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (hcurl : CurlDetected q R u)
    (hr : ProfileRegular q R (Dictionary.FreeSource.responseProfile q R u)) :
    CanonicalCoupling q R V
      (corrDeriv q R (Dictionary.FreeSource.responseProfile q R u)) := by
  apply canonicalCoupling_of_line V _ u hline
  rw [corrDeriv_profile_form q R _ hr u]
  exact ne_of_gt ((Dictionary.FreeSource.adaptive_pos_iff q R u).mpr hcurl)

/-- This is the NEW missing geometric premise on the canonical path. No source
recurrence, cancellation estimate, Fourier normalization or derivative occurs in it. -/
def CofinalCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R (uthPath (2^j) R) u ∧
      CurlDetected (2^j) R u

/-- The free path may be left-only or otherwise asymmetric, but its start and
negative direction must be proved for that same path. -/
def CofinalAnyPathCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u

theorem cofinalAnyProfileCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalCurlLine) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, u, hline, hcurl⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, Dictionary.FreeSource.responseProfile (2^j) R u,
    canonicalCoupling_of_curlDetected (uthPath _ _) u hline hcurl
      (hr (2^j) R (by positivity) hR hR18 _)⟩

theorem cofinalAnyPathCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalAnyPathCurlLine) :
    CofinalAnyPathCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, u, hline, hcurl⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
    Dictionary.FreeSource.responseProfile (2^j) R u,
    canonicalCoupling_of_curlDetected V u hline hcurl
      (hr (2^j) R (by positivity) hR hR18 _)⟩

#print axioms responseProfile_eq
#print axioms profileData
#print axioms ProfileRegular
#print axioms RegularityFacts
#print axioms bulkD_zero_source
#print axioms bulkData_zero
#print axioms corrDeriv_profile_form
#print axioms canonicalCoupling_of_curlDetected
#print axioms CofinalCurlLine
#print axioms CofinalAnyPathCurlLine
#print axioms cofinalAnyProfileCoupling_of_curlLine
#print axioms cofinalAnyPathCoupling_of_curlLine
end AdalyFormal.Round10.Assembly.R3
