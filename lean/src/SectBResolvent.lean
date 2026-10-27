import SectBGraph
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HConstruction.SectBAstra
open AdalyFormal.Target.ClayStatement
open HConstruction.GenK HConstruction.SectBBase
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

/-- Uniform inverse estimate for the EXISTING choice-defined site inverse. -/
theorem flatGPrime_bound (k : ℕ) (f : Site M (n := n)) :
    ‖flatGPrime M hn k f‖ ≤ 3*‖f‖ := by
  have h := flatDeltaPrime_coercive M hn k (flatGPrime M hn k f)
  rw [flatDeltaPrime_flatGPrime] at h
  have hi := real_inner_le_norm (flatGPrime M hn k f) f
  have h0 := norm_nonneg (flatGPrime M hn k f)
  have hf := norm_nonneg f
  nlinarith

theorem flatGPrime_opNorm (k : ℕ) : ‖flatGPrime M hn k‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (flatGPrime_bound M hn k)

/-- The gradient is the physical gradient n∂, not an unweighted O(n) estimate. -/
theorem flatGPrime_gradient_sq (k : ℕ) (f : Site M (n := n)) :
    ‖grad M (flatGPrime M hn k f)‖^2 ≤ 3*‖f‖^2 := by
  let u := flatGPrime M hn k f
  have he : ‖grad M u‖^2 ≤ (inner ℝ u f : ℝ) := by
    have hh : (inner ℝ u (flatDeltaPrime M k u) : ℝ) =
        ‖grad M u‖^2 + (topWeight k*(n:ℝ)^3)*‖flatQPrime M u‖^2 := by
      simp only [flatDeltaPrime, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
        siteDelta, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    have hu : flatDeltaPrime M k u = f := flatDeltaPrime_flatGPrime M hn k f
    rw [hu] at hh
    have hpos : 0 ≤ (topWeight k*(n:ℝ)^3)*‖flatQPrime M u‖^2 :=
      mul_nonneg (mul_nonneg (topWeight_pos k).le (by positivity)) (sq_nonneg _)
    linarith
  have hi := real_inner_le_norm u f
  have hb := mul_le_mul_of_nonneg_right (flatGPrime_bound M hn k f) (norm_nonneg f)
  dsimp [u] at he hi
  nlinarith

theorem flatGPrime_gradient_opNorm (k : ℕ) :
    ‖(grad M).comp (flatGPrime M hn k)‖ ≤ Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  have hs := flatGPrime_gradient_sq M hn k f
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hmul : 0 ≤ Real.sqrt 3 * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  simp only [ContinuousLinearMap.comp_apply]
  nlinarith [norm_nonneg (grad M (flatGPrime M hn k f))]

/-- The other first-derivative estimate and the energy contraction, proved on
actual fields by the inverse equation (no postulated adjoint/inverse budget). -/
theorem flatGPrime_divergence_estimates (k : ℕ) (A : Fine M (n := n)) :
    ‖flatGPrime M hn k ((grad M).adjoint A)‖^2 ≤ 3*‖A‖^2 ∧
    ‖grad M (flatGPrime M hn k ((grad M).adjoint A))‖ ≤ ‖A‖ := by
  let u := flatGPrime M hn k ((grad M).adjoint A)
  have hu : flatDeltaPrime M k u = (grad M).adjoint A :=
    flatDeltaPrime_flatGPrime M hn k _
  have he : (inner ℝ u (flatDeltaPrime M k u) : ℝ) =
      ‖grad M u‖^2 + (topWeight k*(n:ℝ)^3)*‖flatQPrime M u‖^2 := by
    simp only [flatDeltaPrime, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
      siteDelta, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hpos : 0 ≤ (topWeight k*(n:ℝ)^3)*‖flatQPrime M u‖^2 :=
    mul_nonneg (mul_nonneg (topWeight_pos k).le (by positivity)) (sq_nonneg _)
  rw [hu, ContinuousLinearMap.adjoint_inner_right] at he
  have hi := real_inner_le_norm (grad M u) A
  have hg : ‖grad M u‖ ≤ ‖A‖ := by
    nlinarith [norm_nonneg (grad M u), norm_nonneg A]
  have hc := flatDeltaPrime_coercive M hn k u
  rw [hu, ContinuousLinearMap.adjoint_inner_right] at hc
  have hm := mul_le_mul_of_nonneg_right hg (norm_nonneg A)
  exact ⟨by nlinarith, hg⟩

theorem flatGPrime_divergence_opNorm (k : ℕ) :
    ‖(flatGPrime M hn k).comp (grad M).adjoint‖ ≤ Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro A
  have h := (flatGPrime_divergence_estimates M hn k A).1
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hm : 0 ≤ Real.sqrt 3*‖A‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  simp only [ContinuousLinearMap.comp_apply]
  nlinarith [norm_nonneg (flatGPrime M hn k ((grad M).adjoint A))]

theorem flatGPrime_gradient_divergence_opNorm (k : ℕ) :
    ‖(grad M).comp ((flatGPrime M hn k).comp (grad M).adjoint)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  simpa only [ContinuousLinearMap.comp_apply, one_mul] using
    (flatGPrime_divergence_estimates M hn k A).2

/-- Physical L² bounds: the same n^-3 fine-measure normalization in source and
output. At the top stratum L^k eta=1, the printed outgoing weights are 1. -/
theorem flatGPrime_physical_bounds (k : ℕ) (f : Site M (n := n)) :
    (1/(n:ℝ)^3)*‖flatGPrime M hn k f‖^2 ≤ 9*((1/(n:ℝ)^3)*‖f‖^2) ∧
    (1/(n:ℝ)^3)*‖grad M (flatGPrime M hn k f)‖^2 ≤
      3*((1/(n:ℝ)^3)*‖f‖^2) := by
  have h0 := flatGPrime_bound M hn k f
  have hs : ‖flatGPrime M hn k f‖^2 ≤ 9*‖f‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) h0 2
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1/(n:ℝ)^3)
  have h2 := mul_le_mul_of_nonneg_left (flatGPrime_gradient_sq M hn k f)
    (by positivity : (0:ℝ) ≤ 1/(n:ℝ)^3)
  constructor <;> nlinarith

omit hn in
/-- Every depth, arbitrary unit extent. The n=2^k specialization is explicit. -/
theorem flat_base_every_depth (k : ℕ) :
    ‖flatGPrime M (by positivity : 0 < 2^k) k‖ ≤ 3 ∧
    ‖(grad M (n := 2^k)).comp (flatGPrime M (by positivity : 0 < 2^k) k)‖ ≤ Real.sqrt 3 ∧
    ‖(flatGPrime M (by positivity : 0 < 2^k) k).comp (grad M).adjoint‖ ≤ Real.sqrt 3 := by
  exact ⟨flatGPrime_opNorm M (by positivity) k,
    flatGPrime_gradient_opNorm M (by positivity) k,
    flatGPrime_divergence_opNorm M (by positivity) k⟩
end HConstruction.SectBAstra
