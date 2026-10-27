import SourceCoeffAxis
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.DeltaKR66
open AdalyFormal.DeltaKR85
open HConstruction.SmallNF
open HConstruction.Circle
open OneStep124

 theorem nu_pauliE2 : nu (pauliE2 : M2) = 1 := by
  have h := assemble_inner 0 1 0 0 1 0
  have hn : ‖pauliE2‖ ^ 2 = 1 := by
    simpa [assemble, real_inner_self_eq_norm_sq] using h
  rw [← EstimatesLayer.NormBounds.norm_eq_nu]
  nlinarith [norm_nonneg pauliE2]

 theorem nu_axis (s : ℝ) : nu ((s • pauliE2 : SuTwo) : M2) = |s| := by
  rw [Submodule.coe_smul, nu_smul, nu_pauliE2, mul_one]

 theorem unit_mem_step (c : CoarseBond witnessL (1*2))
    (u : {z : PeriodicLatticeSite witnessL // z ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice witnessL 1})
    (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) : u.1 ∈ stepBlockOf c.1.1 1 2 := by
  rw [stepBlockOf_one]
  simpa [unitSitesOf] using hu

 def meanAngle (c : CoarseBond witnessL (1*2)) : ℝ :=
  ∑ u ∈ unitSitesOf 1 (1*2) c.1.1,
    (1 / ((unitSitesOf 1 (1*2) c.1.1).card : ℝ)) * ((loopWord c u.1 : ℝ) * theta)

 theorem source_Z (c : CoarseBond witnessL (1*2)) :
    (sourcePrincipalLogData 1 2 chosenU).Z c = meanAngle c • pauliE2 := by
  unfold LogData.Z meanAngle
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [source_Zx c u.1 (unit_mem_step c u hu), smul_smul]

 theorem source_Zx_small (c : CoarseBond witnessL (1*2))
    (x : PeriodicLatticeSite witnessL) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    nu ((sourcePrincipalLogData 1 2 chosenU).Zx c x : M2) < Real.pi := by
  rw [source_Zx c x hx, nu_axis]
  rcases loopWord_values c x hx with h | h | h
  all_goals rw [h]; first | simpa [abs_of_pos theta_pos] using theta_lt_pi | simpa using Real.pi_pos

 theorem chosen_card (c : CoarseBond witnessL (1*2)) :
    (unitSitesOf 1 (1*2) c.1.1).card = 8 := by
  exact unitSitesOf_card_eq (by norm_num) c.1.2 (by decide)

 theorem chosen_E1_axis (c : CoarseBond witnessL (1*2))
    (x : PeriodicLatticeSite witnessL) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c x pauliE2 = 0 := by
  apply coeff_E1_axis chosenU
  · rw [source_Z]; exact ad_axis _ _
  · rw [source_Zx c x hx]; exact ad_axis _ _
  · exact source_Zx_small c x hx

 theorem chosen_E2_axis (c : CoarseBond witnessL (1*2))
    (x : PeriodicLatticeSite witnessL) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c x pauliE2 = 0 := by
  apply coeff_E2_axis chosenU
  · rw [source_Z]; exact ad_axis _ _
  · rw [source_Zx c x hx]; exact ad_axis _ _
  · exact source_Zx_small c x hx

 theorem chosen_E3_axis (c : CoarseBond witnessL (1*2)) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E3 c pauliE2 = 0 := by
  apply coeff_E3_axis chosenU
  · rw [source_Z]; exact ad_axis _ _
  · intro u hu; rw [source_Zx c u.1 (unit_mem_step c u hu)]; exact ad_axis _ _
  · intro u hu; exact source_Zx_small c u.1 (unit_mem_step c u hu)
  · rw [chosen_card]; norm_num

#print axioms source_Z
#print axioms source_Zx_small
#print axioms chosen_E1_axis
#print axioms chosen_E2_axis
#print axioms chosen_E3_axis
end HConstruction.Coeff
