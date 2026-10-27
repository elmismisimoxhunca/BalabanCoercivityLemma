import ClosedForms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace EstimatesLayer.NormBounds
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.SuTwoInner
open OneStep124 (adOp gOp gInvOp expOp)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

/-- Explicit, non-sharp, continuous-at-zero majorant when assigned the separate value 1 at zero. -/
def gBound (r : ℝ) : ℝ := 1 + |Real.sin r * Real.cos r / r| + |Real.sin r ^ 2 / r|

theorem block_norm_le (Z : SuTwo) (h : 0 < nu (Z : M2)) (a b : ℝ) :
    ‖P Z + a • Q Z + b • J Z‖ ≤ 1 + |a| + |b| := by
  calc ‖P Z + a • Q Z + b • J Z‖ ≤ ‖P Z + a • Q Z‖ + ‖b • J Z‖ := norm_add_le _ _
    _ ≤ (‖P Z‖ + ‖a • Q Z‖) + ‖b • J Z‖ := by gcongr; exact norm_add_le _ _
    _ = (‖P Z‖ + |a| * ‖Q Z‖) + |b| * ‖J Z‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 + |a| * 1) + |b| * 1 := by
      gcongr
      · exact norm_P_le Z h
      · exact norm_Q_le Z h
      · exact norm_J_le Z h
    _ = 1 + |a| + |b| := by ring

theorem norm_g_neg_le (Z : SuTwo) (h : 0 < nu (Z : M2)) :
    ‖gOp (-(adOp Z))‖ ≤ gBound (nu (Z : M2)) := by
  rw [g_neg_block Z h]
  exact block_norm_le Z h _ _

theorem norm_g_pos_le (Z : SuTwo) (h : 0 < nu (Z : M2)) :
    ‖gOp (adOp Z)‖ ≤ gBound (nu (Z : M2)) := by
  have hn : nu ((-Z : SuTwo) : M2) = nu (Z : M2) := nu_neg _
  have hh := norm_g_neg_le (-Z) (by rwa [hn])
  simpa only [ad_neg, neg_neg, hn] using hh

theorem norm_gInv_neg_le (Z : SuTwo) (h : 0 < nu (Z : M2))
    (hs : Real.sin (nu (Z : M2)) ≠ 0) :
    ‖gInvOp (-(adOp Z))‖ ≤ 1 + nu (Z : M2) + nu (Z : M2) / |Real.sin (nu (Z : M2))| := by
  rw [gInv_neg_block Z h hs, inverseBlock]
  have hb := block_norm_le Z h
    (nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))) (-nu (Z : M2))
  have hc : |nu (Z : M2) * Real.cos (nu (Z : M2)) / Real.sin (nu (Z : M2))| ≤
      nu (Z : M2) / |Real.sin (nu (Z : M2))| := by
    rw [abs_div, abs_mul, abs_of_pos h]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.abs_cos_le_one (nu (Z : M2))]) (abs_nonneg _)
  rw [abs_neg, abs_of_pos h] at hb
  linarith

theorem norm_gInv_pos_le (Z : SuTwo) (h : 0 < nu (Z : M2))
    (hs : Real.sin (nu (Z : M2)) ≠ 0) :
    ‖gInvOp (adOp Z)‖ ≤ 1 + nu (Z : M2) + nu (Z : M2) / |Real.sin (nu (Z : M2))| := by
  have hn : nu ((-Z : SuTwo) : M2) = nu (Z : M2) := nu_neg _
  have hh := norm_gInv_neg_le (-Z) (by rwa [hn]) (by rwa [hn])
  simpa only [ad_neg, neg_neg, hn] using hh

theorem norm_exp_neg_le (Z : SuTwo) : ‖expOp (-(adOp Z))‖ ≤ 1 := by
  simpa only [ad_neg] using norm_exp_le (-Z)

/-- Derived first-cut blow-up bound. The upper endpoint is STRICT. -/
theorem scalar_first_cut (r : ℝ) (hl : Real.pi / 2 ≤ r) (hu : r < Real.pi) :
    1 + r + r / |Real.sin r| ≤
      (Real.pi / 2 + Real.pi ^ 2) / (Real.pi - r) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hl
  have hd : 0 < Real.pi - r := sub_pos.mpr hu
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hu
  have hj := Real.mul_le_sin (x := Real.pi - r) (le_of_lt hd) (by linarith : Real.pi - r ≤ Real.pi / 2)
  rw [Real.sin_pi_sub] at hj
  rw [abs_of_pos hsin]
  have hdiv : r / Real.sin r ≤ r * Real.pi / (2 * (Real.pi - r)) := by
    calc r / Real.sin r ≤ r / (2 / Real.pi * (Real.pi - r)) :=
        div_le_div_of_nonneg_left (le_of_lt hr) (by positivity) hj
      _ = r * Real.pi / (2 * (Real.pi - r)) := by field_simp <;> ring
  have hf : 1 + r + r * Real.pi / (2 * (Real.pi - r)) ≤
      (Real.pi / 2 + Real.pi ^ 2) / (Real.pi - r) := by
    apply (le_div_iff₀ hd).mpr
    have hm : (1 + r) * (Real.pi - r) ≤ (1 + Real.pi) * (Real.pi / 2) := by
      apply mul_le_mul (by linarith) (by linarith) (le_of_lt hd) (by positivity)
    have hcan : (r * Real.pi / (2 * (Real.pi - r))) * (Real.pi - r) = r * Real.pi / 2 := by
      field_simp [ne_of_gt hd]
    rw [add_mul, hcan]
    nlinarith
  linarith

theorem norm_gInv_first_cut (Z : SuTwo)
    (hl : Real.pi / 2 ≤ nu (Z : M2)) (hu : nu (Z : M2) < Real.pi) :
    ‖gInvOp (-(adOp Z))‖ ≤
      (Real.pi / 2 + Real.pi ^ 2) / (Real.pi - nu (Z : M2)) := by
  have hr : 0 < nu (Z : M2) := lt_of_lt_of_le (by positivity) hl
  exact (norm_gInv_neg_le Z hr (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr hu))).trans
    (scalar_first_cut _ hl hu)

/-- The removable zero case is the identity, not the singular-inverse convention. -/
theorem operators_zero :
    gOp (adOp (0 : SuTwo)) = 1 ∧ gInvOp (adOp (0 : SuTwo)) = 1 ∧
      expOp (adOp (0 : SuTwo)) = 1 := by
  rw [AdalySI1.DexpRodrigues.adOp_zero_eq,
    AdalySI1.DexpRodrigues.gOp_zero_eq, AdalySI1.Adjoint.expOp_zero_eq,
    OneStep124.gInvOp, AdalySI1.DexpRodrigues.gOp_zero_eq]
  simp

/-- Unified g bound, including r=0, where gBound 0=1. -/
theorem norm_g_both (Z : SuTwo) :
    ‖gOp (adOp Z)‖ ≤ gBound (nu (Z : M2)) ∧
    ‖gOp (-(adOp Z))‖ ≤ gBound (nu (Z : M2)) := by
  by_cases hz : Z = 0
  · subst hz
    have hn : nu ((0 : SuTwo) : M2) = 0 := (nu_eq_zero_iff _).mpr rfl
    rw [AdalySI1.DexpRodrigues.adOp_zero_eq, neg_zero,
      AdalySI1.DexpRodrigues.gOp_zero_eq, hn]
    have hi : ‖(1 : SuTwo →L[ℝ] SuTwo)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa [gBound] using And.intro hi hi
  · have hr : 0 < nu (Z : M2) := by
      have hn : nu (Z : M2) ≠ 0 := fun he => hz (Subtype.ext ((nu_eq_zero_iff _).mp he))
      exact lt_of_le_of_ne (nu_nonneg _) (Ne.symm hn)
    exact ⟨norm_g_pos_le Z hr, norm_g_neg_le Z hr⟩

#print axioms operators_zero
#print axioms norm_g_both
#print axioms norm_g_neg_le
#print axioms norm_g_pos_le
#print axioms norm_gInv_neg_le
#print axioms norm_gInv_pos_le
#print axioms norm_exp_neg_le
#print axioms scalar_first_cut
#print axioms norm_gInv_first_cut
end EstimatesLayer.NormBounds
