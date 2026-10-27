import JointKernel
set_option autoImplicit false
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant)

/-- Source precision, in FORM coordinates on the unweighted H,K. The existence
proof fixes the native Q and the full physical quadratic form. Not scalar data. -/
noncomputable def nativeData (bc : BaseConstant) : BalabanCovarianceData H (CFL2 witnessL 2) :=
  Classical.choose (native_datum_exists bc.a bc.a_pos)

theorem nativeData_identified (bc : BaseConstant) :
    (nativeData bc).Ginv = basePrecision bc.a ∧
    (nativeData bc).Q = nativeLinearQ (trivialU witnessL) 2 ∧
    (nativeData bc).Qstar = (nativeLinearQ (trivialU witnessL) 2).adjoint :=
  Classical.choose_spec (native_datum_exists bc.a bc.a_pos)

lemma siteR_adjoint : siteR.adjoint = siteR := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (siteR_selfAdjoint x y).symm

lemma gauge_precision_identity : gaugeConstraint.adjoint.comp gaugeConstraint =
    flatGrad.comp (siteR.comp flatGrad.adjoint) := by
  ext A
  simp only [gaugeConstraint, ContinuousLinearMap.adjoint_comp, siteR_adjoint,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]
  have hid := congrArg (fun T : S →L[ℝ] S => T (flatGrad.adjoint A)) siteR_idempotent
  exact congrArg flatGrad hid

/-- The literal source precision in VALUE coordinates; fine eta^3=1/8. -/
noncomputable def physicalPrecision (bc : BaseConstant) : H →L[ℝ] H :=
  flatDelta + flatGrad.comp (siteR.comp flatGrad.adjoint) +
    physicalQstar.comp (bc.a • nativeLinearQ (trivialU witnessL) 2)

lemma physicalPrecision_density (bc : BaseConstant) :
    physicalPrecision bc = (8 : ℝ) • (nativeData bc).Ginv := by
  rw [(nativeData_identified bc).1]
  ext A
  simp only [physicalPrecision, basePrecision, physicalQstar,
    ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_smul,
    smul_add, smul_smul]
  have h := congrArg (fun T : H →L[ℝ] H => T A) gauge_precision_identity
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  module

/-- Actual G0=(Delta+DRD*+Q*_phys aQ)^(-1), not inverse bare Delta. -/
noncomputable def physicalG0 (bc : BaseConstant) : H →L[ℝ] H :=
  (1/8 : ℝ) • (nativeData bc).Gstar

theorem physicalG0_rightInverse (bc : BaseConstant) (A : H) :
    physicalPrecision bc (physicalG0 bc A) = A := by
  rw [physicalPrecision_density]
  simp only [physicalG0, smul_apply, map_smul, smul_smul, (nativeData bc).Ginv_Gstar]
  norm_num

theorem physicalG0_leftInverse (bc : BaseConstant) (A : H) :
    physicalG0 bc (physicalPrecision bc A) = A := by
  rw [physicalPrecision_density]
  simp only [physicalG0, smul_apply, map_smul, smul_smul, (nativeData bc).Gstar_Ginv]
  norm_num

theorem physicalG0_unique (bc : BaseConstant) (G : H →L[ℝ] H)
    (hG : ∀ A, physicalPrecision bc (G A) = A) : G = physicalG0 bc := by
  ext A
  calc
    G A = physicalG0 bc (physicalPrecision bc (G A)) := (physicalG0_leftInverse bc _).symm
    _ = physicalG0 bc A := by rw [hG]

theorem physicalPrecision_strict (bc : BaseConstant) (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (physicalPrecision bc A) := by
  rw [physicalPrecision_density, (nativeData_identified bc).1]
  simp only [smul_apply,inner_smul_right]
  exact mul_pos (by norm_num) (basePrecision_positive bc.a bc.a_pos A hA)

theorem physicalG0_strict (bc : BaseConstant) (A : H) (hA : A ≠ 0) :
    (0 : ℝ) < inner ℝ A (physicalG0 bc A) := by
  have hn : physicalG0 bc A ≠ 0 := by
    intro hz
    have h := physicalG0_rightInverse bc A
    rw [hz,map_zero] at h
    exact hA h.symm
  have h := physicalPrecision_strict bc (physicalG0 bc A) hn
  rw [physicalG0_rightInverse,real_inner_comm] at h
  exact h

/-- Source-forced zero J-correction at U=1, now with a CONCRETE G0. -/
noncomputable def physicalG1 (bc : BaseConstant) : H →L[ℝ] H :=
  HConstruction.Covariance.Reproduced.gOneOfNeumann (physicalG0 bc) flatPerturbation

theorem physicalG1_eq_G0 (bc : BaseConstant) : physicalG1 bc = physicalG0 bc :=
  flat_neumann_eq_base _

theorem physicalG1_series (bc : BaseConstant) :
    physicalG1 bc = ∑' n : ℕ, physicalG0 bc * (flatPerturbation * physicalG0 bc)^n :=
  flat_neumann_eq_tsum _

/-- Density transport preserves the source G1 Q* product exactly. -/
theorem physical_product (bc : BaseConstant) (B : CFL2 witnessL 2) :
    physicalG1 bc (physicalQstar B) = (nativeData bc).Gstar ((nativeData bc).Qstar B) := by
  rw [physicalG1_eq_G0, (nativeData_identified bc).2.2]
  simp only [physicalG0, physicalQstar, smul_apply, map_smul, smul_smul]
  norm_num

theorem physical_Schur (bc : BaseConstant) (B : CFL2 witnessL 2) :
    (nativeData bc).Comp B = nativeLinearQ (trivialU witnessL) 2
      (physicalG1 bc (physicalQstar B)) := by
  rw [physical_product, ← (nativeData_identified bc).2.1]
  exact (nativeData bc).Comp_eq B

theorem physical_solutionOperator (bc : BaseConstant) (B : CFL2 witnessL 2) :
    solutionOperator (nativeData bc) B = physicalG1 bc
      (physicalQstar ((nativeData bc).CompInv B)) :=
  (physical_product bc _).symm

/-- Reuses the existing variationalQext. It now has identity first jet
UNCONDITIONALLY, but this alone does not identify the source D-tilde. -/
theorem physical_variational_firstJet (bc : BaseConstant) (B : CFL2 witnessL 2)
    (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond witnessL (1 * 2)) :
    HasDerivAt (fun t : ℝ => ((cfl2Equiv 2
      (variationalQext (trivialU witnessL) 2 (nativeData bc) (t • B)) c :
      AdalyFormal.Balaban.CovariantOperators.SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2))
      ((cfl2Equiv 2 B c : AdalyFormal.Balaban.CovariantOperators.SuTwo) :
        AdalyFormal.Balaban.SuTwoLogExp.M2) 0 :=
  variationalQext_identified_firstJet _ (nativeData_identified bc).2.1 B c
end HConstruction.DRepair
