/-! Assembly-only final application of the previously compiled round-9 bridge.
The full concatenation is not compiled on this memory-limited host.
CofinalDominatedSource is NOT proved. -/
namespace AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round9.Guarded.QualitativeR2Joint

theorem goalNeg2_of_cofinalDominatedSource (h : CofinalDominatedSource) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling (cofinalAnyProfileCoupling_of_dominatedSource h)

theorem goalNeg2_of_cofinalSourceFamily (h : CofinalSourceFamily) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling (cofinalAnyProfileCoupling_of_sourceFamily h)

#print axioms goalNeg2_of_cofinalSourceFamily
#print axioms goalNeg2_of_cofinalDominatedSource
end AdalyFormal.Round10.Assembly.R2
