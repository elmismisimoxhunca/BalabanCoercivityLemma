import DK3FineSecond
import DK3FineSourceWitness
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000
noncomputable section
namespace HConstruction.DK3.FineScale
open Physical (deltaU covCurl covGrad deltaU_flat_bilinear deltaU_flat_energy)
open CovarianceScale (incomingQ)
open HConstruction.Predicate HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
attribute [local irreducible] precision deltaU covCurl gaugeConstraintU incomingQ
  sourceFunctional secondDeltaPort perturbationPort

/-- Negative normalization test: treating the eta-one source as a VALUE vector
at eta=1/8 fails on every nonzero member of the actual family. -/
theorem unscaled_source_rejected (t : ℝ) (ht : t ≠ 0) : JF t ≠ sourceFunctional t := by
  intro h
  have hz : (511 : ℝ) • sourceFunctional t = 0 := by
    have he : (511 : ℝ) • sourceFunctional t = JF t - sourceFunctional t := by
      unfold JF
      module
    rw [he,h,sub_self]
  exact sourceFunctional_nonzero t ht ((smul_eq_zero.mp hz).resolve_left (by norm_num))

def constantField : F := bfl2Equiv.symm (fun _ => suTwoWitness)

theorem constantField_nonzero : constantField ≠ 0 := by
  intro h
  have hv := congrArg (fun A : F => bfl2Equiv A (origin,0)) h
  exact suTwoWitness_ne_zero hv

theorem flatCurl_constant : covCurl (trivialU fineL) constantField = 0 := by
  apply (fiberEquiv _).injective
  funext p
  simp [Physical.covCurl,constantField,AdalyFormal.Balaban.CovariantOperators.curlCovariantLM,
    AdalyFormal.Balaban.CovariantOperators.curlValueCovariant,
    trivialU,AdalyFormal.Balaban.CovariantOperators.RMap_one]

theorem flatDelta_constant : deltaU (U 0) constantField = 0 := by
  apply ext_inner_left ℝ
  intro B
  rw [U_zero, deltaU_flat_bilinear, flatCurl_constant]
  simp

/-- A genuine fine-carrier negative witness. Bare Delta is not a covariance
precision; the full gauge and incoming-mass terms cannot be skipped. -/
theorem bareDelta_no_left_inverse : ¬ ∃ G : F →L[ℝ] F,
    ∀ A, G (deltaU (U 0) A) = A := by
  rintro ⟨G,hG⟩
  have h := hG constantField
  rw [flatDelta_constant,map_zero] at h
  exact constantField_nonzero h.symm

theorem precision_flat_energy (a : ℝ) (A : F) :
    (inner ℝ A (precision 0 a A) : ℝ) = ‖covCurl (trivialU fineL) A‖^2 +
      ‖gaugeConstraintU 0 A‖^2 + 512*a*‖incomingQ 0 A‖^2 := by
  unfold precision
  rw [← gaugeU_identity]
  simp only [_root_.add_apply, inner_add_right, U_zero, deltaU_flat_energy,
    CovarianceScale.incomingPhysicalAdjoint, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, map_smul, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  ring

/-- Exact remaining FLAT inverse gate, on the full fine carrier, not a
rank-deficient K-pullback. This theorem DOES NOT assert the joint kernel is zero. -/
theorem precision_flat_kernel_iff (a : ℝ) (ha : 0 < a) (A : F) :
    precision 0 a A = 0 ↔
      covCurl (trivialU fineL) A = 0 ∧ gaugeConstraintU 0 A = 0 ∧ incomingQ 0 A = 0 := by
  constructor
  · intro h
    have he := precision_flat_energy a A
    rw [h,inner_zero_right] at he
    have hc := sq_nonneg ‖covCurl (trivialU fineL) A‖
    have hg := sq_nonneg ‖gaugeConstraintU 0 A‖
    have hq := sq_nonneg ‖incomingQ 0 A‖
    have hm : 0 ≤ 512*a*‖incomingQ 0 A‖^2 := mul_nonneg (mul_nonneg (by norm_num) ha.le) hq
    have hcz : covCurl (trivialU fineL) A = 0 := norm_eq_zero.mp (by nlinarith)
    have hgz : gaugeConstraintU 0 A = 0 := norm_eq_zero.mp (by nlinarith)
    have hqz : incomingQ 0 A = 0 := by
      apply norm_eq_zero.mp
      have hp : 0 < 512*a := by positivity
      have hz : ‖incomingQ 0 A‖^2 = 0 := by nlinarith
      nlinarith
    exact ⟨hcz,hgz,hqz⟩
  · rintro ⟨hc,hg,hq⟩
    have hd : deltaU (U 0) A = 0 := by
      apply ext_inner_left ℝ
      intro B
      rw [U_zero,deltaU_flat_bilinear,hc]
      simp
    unfold precision
    rw [← gaugeU_identity]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
      hd,hg,hq,map_zero,smul_zero,zero_add]

/-- Necessary trust check for any eventual fine G0. -/
theorem physicalG0_forces_flat_jointKernel (h : HasPhysicalG0 0 1) (A : F)
    (hc : covCurl (trivialU fineL) A = 0) (hg : gaugeConstraintU 0 A = 0)
    (hq : incomingQ 0 A = 0) : A = 0 := by
  obtain ⟨G,_,hG⟩ := h
  have hn := (precision_flat_kernel_iff 1 (by norm_num) A).mpr ⟨hc,hg,hq⟩
  have he := congrArg (fun T : F →L[ℝ] F => T A) hG
  change G (precision 0 1 A) = A at he
  rw [hn,map_zero] at he
  exact he.symm

#print axioms unscaled_source_rejected
#print axioms bareDelta_no_left_inverse
#print axioms precision_flat_kernel_iff
end HConstruction.DK3.FineScale
