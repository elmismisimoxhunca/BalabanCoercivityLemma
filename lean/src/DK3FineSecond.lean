import DK3FineGauge

/-! The source contraction of the genuine fine Hessian. The K -> F post-map
is EXPLICIT: this file does not invent a physical intermediate H before its
G0/Schur inverse gates have been proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000
noncomputable section
namespace HConstruction.DK3.FineScale
open Physical (fromBil inner_fromBil deltaU)
open CovarianceScale (fineInner incomingQ)
attribute [local irreducible] sourceFunctional averagingHessian averagingC2 gaugePi
  Physical.deltaU Physical.fromBil

section Bilinear
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def contractedBil (post : V →L[ℝ] E) (hess : E →L[ℝ] E →L[ℝ] V) (J : E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ := {
  toFun := fun A => (innerSL ℝ J).toLinearMap.comp
    (post.toLinearMap.comp (hess A).toLinearMap)
  map_add' := by
    intro A B
    ext C
    change inner ℝ J (post (hess (A+B) C)) = inner ℝ J (post (hess A C)) + inner ℝ J (post (hess B C))
    simp only [map_add, _root_.add_apply, inner_add_right]
  map_smul' := by
    intro r A
    ext B
    change inner ℝ J (post (hess (r • A) B)) = r * inner ℝ J (post (hess A B))
    simp only [map_smul, _root_.smul_apply, inner_smul_right] }

theorem contractedBil_apply (post : V →L[ℝ] E) (hess : E →L[ℝ] E →L[ℝ] V) (J A B : E) :
    contractedBil post hess J A B = inner ℝ J (post (hess A B)) := rfl
end Bilinear

/-- Fine F -> F Riesz correction, with an honest pending intermediate-H slot.
This is the internal second jet, NOT DK3.Unit.unitD2 : K -> K. -/
def secondDeltaPort (t : ℝ) (H : K →L[ℝ] F) : F →L[ℝ] F :=
  let b := contractedBil H (averagingHessian t) (sourceFunctional t)
  (512 : ℝ) • fromBil ((1/2 : ℝ) • (b + b.flip))

theorem secondDeltaPort_bilinear (t : ℝ) (H : K →L[ℝ] F) (A B : F) :
    (inner ℝ A (secondDeltaPort t H B) : ℝ) = 256 *
      (inner ℝ (sourceFunctional t) (H (averagingHessian t A B)) +
       inner ℝ (sourceFunctional t) (H (averagingHessian t B A))) := by
  simp only [secondDeltaPort, _root_.smul_apply, inner_smul_right, inner_fromBil,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply,
    contractedBil_apply, smul_eq_mul]
  ring

theorem secondDeltaPort_energy (t : ℝ) (H : K →L[ℝ] F) (A : F) :
    fineInner A (secondDeltaPort t H A) = 2 * fineInner (H (averagingC2 t A)) (JF t) := by
  rw [JF_functional]
  unfold fineInner
  rw [secondDeltaPort_bilinear, averagingC2, map_smul, real_inner_smul_left, real_inner_comm]
  ring

theorem secondDeltaPort_selfAdjoint (t : ℝ) (H : K →L[ℝ] F) (A B : F) :
    (inner ℝ (secondDeltaPort t H A) B : ℝ) = inner ℝ A (secondDeltaPort t H B) := by
  rw [real_inner_comm, secondDeltaPort_bilinear, secondDeltaPort_bilinear]
  ring

theorem secondDeltaPort_zero (H : K →L[ℝ] F) : secondDeltaPort 0 H = 0 := by
  ext A
  apply ext_inner_left ℝ
  intro B
  rw [secondDeltaPort_bilinear, sourceFunctional_zero]
  simp

/-- Two-term source perturbation, retaining BOTH Pi factors and an explicit H. -/
def perturbationPort (t : ℝ) (H : K →L[ℝ] F) : F →L[ℝ] F :=
  deltaPrimePi t + sandwich (gaugePi t) (secondDeltaPort t H)

theorem perturbationPort_zero (H : K →L[ℝ] F) : perturbationPort 0 H = 0 := by
  unfold perturbationPort sandwich
  rw [deltaPrimePi_zero, secondDeltaPort_zero]
  ext A
  simp

/-- Exact fine form, useful for checking any future certified G0/G1 implementation. -/
theorem perturbed_form (t : ℝ) (H : K →L[ℝ] F) (A : F) :
    fineInner A ((precision t 1 - perturbationPort t H) A) =
      fineInner (gaugePi t A) (deltaU (U t) (gaugePi t A)) -
      2 * fineInner (H (averagingC2 t (gaugePi t A))) (JF t) +
      (1/512 : ℝ) * ‖gaugeConstraintU t A‖^2 + ‖incomingQ t A‖^2 := by
  have hsecond := secondDeltaPort_energy t H (gaugePi t A)
  unfold fineInner at hsecond ⊢
  unfold precision perturbationPort deltaPrimePi
  rw [← gaugeU_identity]
  simp only [_root_.sub_apply, _root_.add_apply, inner_sub_right, inner_add_right,
    deltaPi_bilinear, sandwich_bilinear, ContinuousLinearMap.comp_apply,
    CovarianceScale.incomingPhysicalAdjoint, _root_.smul_apply, one_smul,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  linarith

#print axioms secondDeltaPort_energy
#print axioms perturbationPort_zero
#print axioms perturbed_form
end HConstruction.DK3.FineScale
