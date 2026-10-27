import PhysicalCovariance
set_option autoImplicit false
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator Ginv_solutionOperator)

lemma flatCurl_grad (f : S) : flatCurl (flatGrad f) = 0 := by
  apply (fiberEquiv _).injective
  funext p
  simp [flatCurl,flatGrad,curlCovariantLM,curlValueCovariant,gradCovariantLM,
    gradValueCovariant,trivialU,RMap_one]
  rw [AdalyFormal.Balaban.LatticeOperators.periodicLatticeShift_comm p.1 (ne_of_lt p.2.2)]
  module

lemma nativeQ_Qprime_grad (f : S) (hf : flatSiteQ f = 0) :
    nativeLinearQ (trivialU witnessL) 2 (flatGrad f) = 0 := by
  apply (cfl2Equiv 2).injective
  funext c
  rw [nativeQ_grad]
  change flatSiteQ f (csMove c.1 c.2) - flatSiteQ f c.1 = 0
  rw [hf]
  simp

/-- The newly constructed physical section satisfies the second source
constraint RD*H1B=0, not only the interpolation QH1B=B. -/
theorem physical_section_gauge (bc : BaseConstant) (B : CFL2 witnessL 2) :
    gaugeConstraint (solutionOperator (nativeData bc) B) = 0 := by
  let A := solutionOperator (nativeData bc) B
  have hm : gaugeConstraint A ∈ gaugeImage :=
    Submodule.starProjection_apply_mem gaugeImage (flatGrad.adjoint A)
  obtain ⟨f,hf,hfe⟩ := hm
  have hf0 : flatSiteQ f = 0 := hf
  have hd : flatSiteDelta f = gaugeConstraint A := hfe
  have hQ := nativeQ_Qprime_grad f hf0
  have hR : gaugeConstraint (flatGrad f) = gaugeConstraint A := by
    change siteR (flatSiteDelta f) = _
    rw [hd]
    exact Submodule.starProjection_eq_self_iff.mpr ⟨f,hf,hfe⟩
  have hstationary : (inner ℝ (flatGrad f) (basePrecision bc.a A) : ℝ) = 0 := by
    rw [← (nativeData_identified bc).1]
    change (inner ℝ (flatGrad f) ((nativeData bc).Ginv (solutionOperator (nativeData bc) B)) : ℝ) = 0
    rw [Ginv_solutionOperator, (nativeData_identified bc).2.2,
      ContinuousLinearMap.adjoint_inner_right,hQ,inner_zero_left]
  have he : (inner ℝ (flatGrad f) (basePrecision bc.a A) : ℝ) =
      (1/8 : ℝ) * ‖gaugeConstraint A‖ ^ 2 := by
    simp only [basePrecision,flatDelta,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      inner_add_right,inner_smul_right,ContinuousLinearMap.adjoint_inner_right,
      flatCurl_grad,hQ,inner_zero_left,hR,real_inner_self_eq_norm_sq]
    ring
  rw [he] at hstationary
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gaugeConstraint A)])
end HConstruction.DRepair
