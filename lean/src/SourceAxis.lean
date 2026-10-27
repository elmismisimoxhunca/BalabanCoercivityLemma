import CoeffClosedForms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open OneStep124
open EstimatesLayer.NormBounds

/-- The source commutator is linear in its base point. -/
theorem ad_smul (r : ℝ) (Z : SuTwo) : adOp (r • Z) = r • adOp Z := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  simp [AdalySI1.DexpRodrigues.adOp_apply_coe, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem ad_axis (r : ℝ) (Z : SuTwo) : adOp (r • Z) Z = 0 := by
  rw [ad_smul]
  simp [ad_self]

/-- Zero-eigenvectors of the actual commutator are fixed by the source g series. -/
theorem g_neg_fixed (Z X : SuTwo) (h : adOp Z X = 0) : gOp (-(adOp Z)) X = X := by
  rw [AdalySI1.GopTransport.gOp_apply_eq_tsum]
  have hp : ∀ n : ℕ, ((adOp Z) ^ (n+1)) X = 0 := by
    intro n
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_zero]
  rw [tsum_eq_single 0]
  · simp [AdalySI1.M2RouteAudit.hCoeff]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hp]
    simp

theorem g_pos_fixed (Z X : SuTwo) (h : adOp Z X = 0) : gOp (adOp Z) X = X := by
  have hh := g_neg_fixed (-Z) X (by simp [ad_neg, h])
  simpa [ad_neg] using hh

theorem exp_fixed (Z X : SuTwo) (h : adOp Z X = 0) : expOp (adOp Z) X = X := by
  have he : expOp (adOp Z) X = ∑' n : ℕ, expCoeff n • ((adOp Z)^n) X :=
    (ContinuousLinearMap.apply ℝ SuTwo X).map_tsum (AdalySI1.Adjoint.expSummable (adOp Z))
  rw [he]
  have hp : ∀ n : ℕ, ((adOp Z) ^ (n+1)) X = 0 := by
    intro n
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_zero]
  rw [tsum_eq_single 0]
  · simp [expCoeff]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    change expCoeff (k+1) • ((adOp Z)^(k+1)) X = 0
    rw [hp, smul_zero]

/-- Includes the removable zero case. The first cut is strict. -/
theorem g_neg_isUnit_small (Z : SuTwo) (h : nu (Z : M2) < Real.pi) :
    IsUnit (gOp (-(adOp Z))) := by
  by_cases hz : Z = 0
  · subst Z
    rw [AdalySI1.DexpRodrigues.adOp_zero_eq, neg_zero, AdalySI1.DexpRodrigues.gOp_zero_eq]
    exact isUnit_one
  · have hr : 0 < nu (Z : M2) := by
      have hn : nu (Z : M2) ≠ 0 := fun he => hz (Subtype.ext ((nu_eq_zero_iff _).mp he))
      exact lt_of_le_of_ne (nu_nonneg _) (Ne.symm hn)
    have hh := inverseBlock_spec Z hr (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr h))
    exact ⟨⟨_, inverseBlock Z, hh.1, hh.2⟩, rfl⟩

theorem g_pos_isUnit_small (Z : SuTwo) (h : nu (Z : M2) < Real.pi) :
    IsUnit (gOp (adOp Z)) := by
  have hh := g_neg_isUnit_small (-Z) (by simpa only [Submodule.coe_neg, nu_neg] using h)
  simpa [ad_neg] using hh

/-- Ring.inverse is used only after proving the source g operator is a unit. -/
theorem gInv_fixed_of_unit (T : SuTwo →L[ℝ] SuTwo) (X : SuTwo)
    (hu : IsUnit (gOp T)) (hx : gOp T X = X) : gInvOp T X = X := by
  have hh := congrArg (fun A : SuTwo →L[ℝ] SuTwo => A X) (Ring.inverse_mul_cancel _ hu)
  simpa [gInvOp, ContinuousLinearMap.mul_apply, hx] using hh

theorem gInv_neg_fixed_small (Z X : SuTwo) (hr : nu (Z : M2) < Real.pi)
    (hx : adOp Z X = 0) : gInvOp (-(adOp Z)) X = X :=
  gInv_fixed_of_unit _ X (g_neg_isUnit_small Z hr) (g_neg_fixed Z X hx)

theorem gInv_pos_fixed_small (Z X : SuTwo) (hr : nu (Z : M2) < Real.pi)
    (hx : adOp Z X = 0) : gInvOp (adOp Z) X = X :=
  gInv_fixed_of_unit _ X (g_pos_isUnit_small Z hr) (g_pos_fixed Z X hx)

#print axioms ad_axis
#print axioms g_neg_fixed
#print axioms g_pos_fixed
#print axioms exp_fixed
#print axioms g_neg_isUnit_small
#print axioms g_pos_isUnit_small
#print axioms gInv_neg_fixed_small
#print axioms gInv_pos_fixed_small
end HConstruction.Coeff
