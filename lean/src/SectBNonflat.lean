import SectBQL2
import SectBPointwise
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK HConstruction.SectBBase HConstruction.SectBAstra
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

omit hn in
private theorem square_difference {E : Type*} [NormedAddCommGroup E]
    (x y : E) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := norm_sub_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y,
    norm_nonneg (x-y)]

/-- A3: strict, depth/volume/mesh-independent floor of the ACTUAL nonflat
single-stratum site operator. No Neumann or derivative-of-U assumption. -/
theorem covDeltaPrime_floor (U : Links M (n := n)) (k : ℕ) (α : ℝ)
    (hsmall : frobSupBond U ≤ α/(n:ℝ)) (f : Site M (n := n)) :
    ((1/6:ℝ)-48*α^2)*‖f‖^2 ≤ (inner ℝ f (covDeltaPrime M U k f) : ℝ) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have he := gradientDrift_sq M hn U α hsmall f
  have hq := qDrift_sq M hn U α hsmall f
  have hg0 : grad M f = covGrad M U f - gradientDrift M U f := by
    simp [gradientDrift]
  have hq0 : flatQPrime M f = covQPrime M U f - qDrift M U f := by
    simp [qDrift]
  have hg := square_difference (covGrad M U f) (gradientDrift M U f)
  have hqs := square_difference (covQPrime M U f) (qDrift M U f)
  rw [← hg0] at hg
  rw [← hq0] at hqs
  have ha := (topWeight_bounds k).2
  have hapos := (topWeight_pos k).le
  have hnf : (n:ℝ)^3*(1/(n:ℝ)^3) = 1 := by field_simp
  have hdiff : ‖grad M f‖^2 + (topWeight k*(n:ℝ)^3)*‖flatQPrime M f‖^2 ≤
      2*(‖covGrad M U f‖^2 + (topWeight k*(n:ℝ)^3)*‖covQPrime M U f‖^2) +
      96*α^2*‖f‖^2 := by
    have hmul := mul_le_mul_of_nonneg_left hqs
      (by positivity : (0:ℝ) ≤ topWeight k*(n:ℝ)^3)
    have herr := mul_le_mul_of_nonneg_left hq
      (by positivity : (0:ℝ) ≤ 2*topWeight k*(n:ℝ)^3)
    have hcoef : 0 ≤ (1-topWeight k)*α^2*‖f‖^2 := by positivity
    nlinarith
  have hf := flatDeltaPrime_coercive M hn k f
  have hflat : (inner ℝ f (flatDeltaPrime M k f) : ℝ) =
      ‖grad M f‖^2 + (topWeight k*(n:ℝ)^3)*‖flatQPrime M f‖^2 := by
    simp only [flatDeltaPrime, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      inner_add_right, inner_smul_right, siteDelta,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hflat] at hf
  rw [covDeltaPrime_form]
  nlinarith
end HConstruction.SectBP1
