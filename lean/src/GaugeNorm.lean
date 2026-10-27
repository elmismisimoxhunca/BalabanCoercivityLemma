import GaugeDual
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
noncomputable section
namespace HConstruction.TransversePos
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Nonflat
open HConstruction.NfRepair.Reproduced HConstruction.G0Final.Locality
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

theorem RMap_norm (U : SU2) (X : SuTwo) : ‖RMap U X‖ = ‖X‖ := (RIsometry U).norm_map X

theorem siteFrame_norm (t : ℝ) (X : S) : ‖siteFrame t X‖ = ‖X‖ := by
  have he : ‖siteFrame t X‖^2 = ‖X‖^2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    change (∑ x : Site, inner ℝ (fiberEquiv _ (siteFrame t X) x) (fiberEquiv _ (siteFrame t X) x)) =
      ∑ x : Site, inner ℝ (fiberEquiv _ X x) (fiberEquiv _ X x)
    apply Finset.sum_congr rfl
    intro x _
    rw [siteFrame_value]
    split_ifs
    · rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, RMap_norm]
    · rfl
  nlinarith [norm_nonneg (siteFrame t X), norm_nonneg X]

theorem siteFrame_opNorm (t : ℝ) : ‖siteFrame t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro X
  rw [siteFrame_norm, one_mul]

theorem covGrad_opNorm (U : PeriodicLinkConfiguration SU2 witnessL) : ‖covGrad U‖ ≤ 64 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro X
  have hp (b : Bond witnessL) : ‖bfl2Equiv (covGrad U X) b‖ ≤ 4*‖X‖ := by
    change ‖(2:ℝ) • (RMap (U b) (fiberEquiv _ X (periodicLatticeShift b.1 b.2)) - fiberEquiv _ X b.1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hn := norm_sub_le (RMap (U b) (fiberEquiv _ X (periodicLatticeShift b.1 b.2))) (fiberEquiv _ X b.1)
    rw [RMap_norm] at hn
    have h1 : ‖fiberEquiv _ X (periodicLatticeShift b.1 b.2)‖ ≤ ‖X‖ := PiLp.norm_apply_le X _
    have h2 : ‖fiberEquiv _ X b.1‖ ≤ ‖X‖ := PiLp.norm_apply_le X _
    linarith
  have he : ‖covGrad U X‖^2 = ∑ b : Bond witnessL, ‖bfl2Equiv (covGrad U X) b‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∑ b : Bond witnessL, inner ℝ (bfl2Equiv (covGrad U X) b) (bfl2Equiv (covGrad U X) b)) = _
    simp only [real_inner_self_eq_norm_sq]
  have hs : (∑ b : Bond witnessL, ‖bfl2Equiv (covGrad U X) b‖^2) ≤
      ∑ _b : Bond witnessL, 16*‖X‖^2 := by
    apply Finset.sum_le_sum
    intro b _
    have hh := hp b
    nlinarith [norm_nonneg (bfl2Equiv (covGrad U X) b), norm_nonneg X]
  have hc : Fintype.card (Bond witnessL) = 192 := by decide +kernel
  rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] at hs
  norm_num at hs
  nlinarith [norm_nonneg (covGrad U X), norm_nonneg X]

theorem gaugeSpan_opNorm (t : ℝ) : ‖gaugeSpan t‖ ≤ 4096 := by
  have hD := covGrad_opNorm (nonflatU t)
  have hW := siteFrame_opNorm t
  have hP : ‖kernelProjection‖ ≤ 1 := Submodule.starProjection_norm_le _
  have h1 := ContinuousLinearMap.opNorm_comp_le (siteFrame t) kernelProjection
  have h2 := ContinuousLinearMap.opNorm_comp_le (covGrad (nonflatU t)).adjoint (covGrad (nonflatU t))
  rw [ContinuousLinearMap.adjoint.norm_map] at h2
  have h3 := ContinuousLinearMap.opNorm_comp_le (siteDeltaU (nonflatU t)) ((siteFrame t).comp kernelProjection)
  have hWP : ‖(siteFrame t).comp kernelProjection‖ ≤ 1 := by
    nlinarith [norm_nonneg (siteFrame t), norm_nonneg kernelProjection]
  have hDD : ‖siteDeltaU (nonflatU t)‖ ≤ 4096 := by
    change ‖(covGrad (nonflatU t)).adjoint.comp (covGrad (nonflatU t))‖ ≤ _
    nlinarith [norm_nonneg (covGrad (nonflatU t))]
  change ‖(siteDeltaU (nonflatU t)).comp ((siteFrame t).comp kernelProjection)‖ ≤ _
  nlinarith [norm_nonneg (siteDeltaU (nonflatU t)), norm_nonneg ((siteFrame t).comp kernelProjection)]

/-- A fixed rational normalization, deliberately conservative, avoids differentiating
an operator norm or the moving gauge projector. -/
theorem fixed_gauge_dual_bound (t : ℝ) (A : H) :
    (1/16777217 : ℝ) * ‖dualGauge t A‖^2 ≤ ‖gaugeConstraintU (nonflatU t) A‖^2 := by
  have h := gauge_dual_bound t A
  have hn := gaugeSpan_opNorm t
  have he : ‖gaugeSpan t‖^2 ≤ (4096:ℝ)^2 := by nlinarith [norm_nonneg (gaugeSpan t)]
  have hm := mul_le_mul_of_nonneg_right he (sq_nonneg ‖gaugeConstraintU (nonflatU t) A‖)
  change (1/16777217 : ℝ) * ‖(gaugeSpan t).adjoint ((covGrad (nonflatU t)).adjoint A)‖^2 ≤ _
  nlinarith

#print axioms RMap_norm
#print axioms siteFrame_norm
#print axioms covGrad_opNorm
#print axioms gaugeSpan_opNorm
#print axioms fixed_gauge_dual_bound
end HConstruction.TransversePos
