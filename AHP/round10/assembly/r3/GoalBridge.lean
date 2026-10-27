/-! HISTORICAL JOIN ONLY: not compiled on this memory-limited worker.
The three regularity inputs and the goal bridges are already round-9 theorems.
The coordinator explicitly requested deferring the full concatenation compile.
No missing cofinal geometric premise is asserted here. -/
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- Exactly the existing round-9 inputs to the compiled arbitrary-profile glue. -/
theorem regularityFacts : RegularityFacts := by
  intro q R hq hR hR18 f
  exact ⟨bulk_H_cont hq (by omega) (dil_admissible hq hR) f,
    bulk_C2_tendsto hq (dil_admissible hq hR) f,
    hasDerivAt_corrDeriv hq hR (by omega) f⟩

theorem corrDeriv_profile_form_all {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u :=
  corrDeriv_profile_form q R f (regularityFacts q R hq hR hR18 f) u

theorem goalNeg2_of_cofinalCurlLine (h : CofinalCurlLine) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling (cofinalAnyProfileCoupling_of_curlLine regularityFacts h)

theorem goalNeg2_of_cofinalAnyPathCurlLine (h : CofinalAnyPathCurlLine) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyPathCoupling (cofinalAnyPathCoupling_of_curlLine regularityFacts h)

#print axioms regularityFacts
#print axioms corrDeriv_profile_form_all
#print axioms goalNeg2_of_cofinalCurlLine
#print axioms goalNeg2_of_cofinalAnyPathCurlLine
end AdalyFormal.Round10.Assembly.R3
