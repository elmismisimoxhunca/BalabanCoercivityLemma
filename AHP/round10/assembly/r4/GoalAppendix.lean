/-! HISTORICAL JOIN ONLY, NOT COMPILED on this memory-limited worker.
The new cofinal hypotheses below are unproved. These are not goal closure. -/
namespace AdalyFormal.Round10.Assembly.R4
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round9.Guarded.QualitativeR2Joint

theorem goalNeg2_of_cofinalNoResponseCancellation
    (h : CofinalNoResponseCancellation) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling
    ((cofinalAnyProfileCoupling_iff_noCancellation R3.regularityFacts).mpr h)

theorem goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (h : CofinalAnyPathNoResponseCancellation) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyPathCoupling
    ((cofinalAnyPathCoupling_iff_noCancellation R3.regularityFacts).mpr h)

#print axioms goalNeg2_of_cofinalNoResponseCancellation
#print axioms goalNeg2_of_cofinalAnyPathNoResponseCancellation
end AdalyFormal.Round10.Assembly.R4
