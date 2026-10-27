/-! HISTORICAL JOIN ONLY. Not compiled here; flat unit is the existing round-9 theorem.
CofinalJetLine and CofinalAnyPathJetLine remain unproved. -/
namespace AdalyFormal.Round10.Assembly.R3
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR2

theorem flatConstraintUnits : FlatConstraintUnits := by
  intro q R hq hR hR18
  have h := dil_N0_unit hq (by omega) (dil_admissible hq hR)
  rw [dataFam_dil_zero] at h
  exact h

theorem goalNeg2_of_cofinalJetLine (h : CofinalJetLine) : GoalNeg2 :=
  goalNeg2_of_cofinalCurlLine (cofinalCurlLine_of_jetLine flatConstraintUnits h)

theorem goalNeg2_of_cofinalAnyPathJetLine (h : CofinalAnyPathJetLine) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyPathCurlLine (cofinalAnyPathCurlLine_of_jetLine flatConstraintUnits h)

#print axioms flatConstraintUnits
#print axioms goalNeg2_of_cofinalJetLine
#print axioms goalNeg2_of_cofinalAnyPathJetLine
end AdalyFormal.Round10.Assembly.R3
