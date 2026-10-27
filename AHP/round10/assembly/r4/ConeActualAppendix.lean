/-! Actual common-profile characterization, with no simple-kernel assumption.
The known round-9 calculus inputs remain explicit through ProfileRegular. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R4
open scoped BigOperators RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Assembly.R3 (ProfileRegular RegularityFacts corrDeriv_profile_form)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

abbrev ProfileSpace (q R : ℕ) := EuclideanSpace ℝ (Bond (scaleUp 2 1 (dilLu q R)))

/-- The exact physical curl-adjoint-curl response, including the coupling factor 2. -/
def responseGradient (q R : ℕ) (u : TwistSpace q R) : ProfileSpace q R :=
  WithLp.toLp 2 (fun b => 2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
    (Dictionary.FreeSource.responseProfile q R u) b)

theorem profileCoupling_gradient (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = ⟪(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫ := by
  classical
  rw [profileCoupling_curl, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change 2 * (∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then
    circulation (Dictionary.FreeSource.responseProfile q R u) p * circulation f p else 0) =
    ∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b
  rw [show (∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b) =
    2 * ∑ b, f b * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring]
  rw [source_sbp]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem double_inner_smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a ^ 2 • x, y⟫ = a ^ 2 * (2 * ⟪x, y⟫) := by
  rw [real_inner_smul_left]
  ring

theorem profileCoupling_smul_input (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (a • u) = a ^ 2 * profileCoupling q R f u := by
  unfold profileCoupling AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling
  simp only [map_smul]
  rw [(C2fullOf_quad (geomOf 2 1 (dilTower q R)) (fun _ => 1)).smul_sq]
  simp only [map_smul]
  exact double_inner_smul (X := TwistSpace q R)
    ((flatData q R).H (vacJet q R u)) (profileSourceStencil q R f) a

theorem responseGradient_smul (q R : ℕ) (a : ℝ) (u : TwistSpace q R) :
    responseGradient q R (a • u) = a ^ 2 • responseGradient q R u := by
  apply ext_inner_left ℝ
  intro f
  rw [inner_smul_right, ← profileCoupling_gradient q R (fun b => f b),
    ← profileCoupling_gradient q R (fun b => f b), profileCoupling_smul_input]

/-- Entire actual crossing kernel; no charged-line or character restriction. -/
def crossingKernel (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R) := (vacA q R V 1 (vacEdge q R V)).ker

/-- This condition is NOT proved for any cofinal family. It rules out convex
cancellation among all unit kernel response gradients, not just individual zeros. -/
def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  (0 : ProfileSpace q R) ∉ responseHull (crossingKernel q R V) (responseGradient q R)

theorem exists_positive_profile_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    (∃ (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ), 0 < c ∧
      ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
        c * ‖u‖ ^ 2 ≤ profileCoupling q R f u) ↔ NoResponseCancellation q R V := by
  rw [NoResponseCancellation, ← common_coercive_iff_notMem_responseHull
    (crossingKernel q R V) (responseGradient q R) (responseGradient_smul q R)]
  constructor
  · rintro ⟨f, c, hc, hf⟩
    refine ⟨InnerProductSpace.toDual ℝ (ProfileSpace q R) (WithLp.toLp 2 f), c, hc, ?_⟩
    intro u hu
    rw [InnerProductSpace.toDual_apply_apply, ← profileCoupling_gradient]
    exact hf u hu
  · rintro ⟨f, c, hc, hf⟩
    let r : ProfileSpace q R := (InnerProductSpace.toDual ℝ (ProfileSpace q R)).symm f
    refine ⟨fun b => r b, c, hc, ?_⟩
    intro u hu
    rw [profileCoupling_gradient]
    change c * ‖u‖ ^ 2 ≤ ⟪r, responseGradient q R u⟫
    rw [InnerProductSpace.toDual_symm_apply]
    exact hf u hu

theorem profileCoupling_neg_profile (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R (fun b => -f b) u = -profileCoupling q R f u := by
  rw [profileCoupling_gradient, profileCoupling_gradient]
  change ⟪-(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫ = _
  exact inner_neg_left _ _

/-- Exact equivalence with the ORIGINAL per-instance coupling premise, assuming
only the already-known regularity facts for these profiles. -/
theorem exists_canonicalCoupling_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hr : ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ,
      CanonicalCoupling q R V (corrDeriv q R f)) ↔ NoResponseCancellation q R V := by
  rw [← exists_positive_profile_iff_noCancellation]
  constructor
  · rintro ⟨f, c, hc, hsign⟩
    rcases hsign with hp | hn
    · refine ⟨f, c, hc, fun u hu => ?_⟩
      rw [← corrDeriv_profile_form q R f (hr f) u]
      exact hp u hu
    · refine ⟨fun b => -f b, c, hc, fun u hu => ?_⟩
      rw [profileCoupling_neg_profile, ← corrDeriv_profile_form q R f (hr f) u]
      exact hn u hu
  · rintro ⟨f, c, hc, hf⟩
    refine ⟨f, c, hc, Or.inl (fun u hu => ?_)⟩
    rw [corrDeriv_profile_form q R f (hr f) u]
    exact hf u hu

/-- Individual detection is necessary, but this theorem does not reverse it. -/
theorem responseGradient_ne_zero_of_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (h : NoResponseCancellation q R V) (u : TwistSpace q R)
    (hu : vacA q R V 1 (vacEdge q R V) u = 0) (hne : u ≠ 0) :
    responseGradient q R u ≠ 0 :=
  response_ne_zero_of_notMem_responseHull (crossingKernel q R V) (responseGradient q R)
    (responseGradient_smul q R) h u hu hne

#print axioms ProfileSpace
#print axioms responseGradient
#print axioms profileCoupling_gradient
#print axioms double_inner_smul
#print axioms profileCoupling_smul_input
#print axioms responseGradient_smul
#print axioms crossingKernel
#print axioms NoResponseCancellation
#print axioms exists_positive_profile_iff_noCancellation
#print axioms profileCoupling_neg_profile
#print axioms exists_canonicalCoupling_iff_noCancellation
#print axioms responseGradient_ne_zero_of_noCancellation
end AdalyFormal.Round10.Assembly.R4
