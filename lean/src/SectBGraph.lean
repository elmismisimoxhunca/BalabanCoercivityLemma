import SectBMean
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HConstruction.SectBAstra
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open HConstruction.GenK HConstruction.SectBBase

/-- Sum the scalar Neumann block estimate over an actual orthonormal basis of su(2).
No matrix-entry independence or volume-dependent norm equivalence is used. -/
theorem vector_graph_bound {L : PeriodicLatticeExtent} (n : ℕ) (hn : 0 < n)
    (hdvd : ∀ μ, n ∣ L μ+1) (f : PeriodicLatticeSite L → SuTwo) :
    ∑ x, ‖f x‖^2 ≤ 3*(n:ℝ)^2 *
      ∑ b : Bond L, ‖f (periodicLatticeShift b.1 b.2) - f b.1‖^2 +
      2*(n:ℝ)^3 * ∑ y ∈ CoarseLattice L n,
        ‖(1/(n:ℝ)^3) • ∑ x ∈ blockOf y n, f x‖^2 := by
  let β := stdOrthonormalBasis ℝ SuTwo
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    scalar_graph_bound n hn hdvd (fun x => inner ℝ (β i) (f x)))
  have hg (i : Fin (Module.finrank ℝ SuTwo)) (b : Bond L) :
      AdalyFormal.Balaban.LatticeOperators.gradValue (fun x => inner ℝ (β i) (f x)) b =
        inner ℝ (β i) (f (periodicLatticeShift b.1 b.2)-f b.1) := by
    simp only [AdalyFormal.Balaban.LatticeOperators.gradValue, inner_sub_right]
  have hq (i : Fin (Module.finrank ℝ SuTwo)) (y : PeriodicLatticeSite L) :
      (1/(n:ℝ)^3) * ∑ x ∈ blockOf y n, inner ℝ (β i) (f x) =
        inner ℝ (β i) ((1/(n:ℝ)^3) • ∑ x ∈ blockOf y n, f x) := by
    simp only [inner_smul_right, inner_sum]
  simp only [hg, hq] at hs
  rw [Finset.sum_comm] at hs
  simp only [β.sum_sq_inner_right] at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  conv_rhs at hs =>
    arg 1; arg 2; rw [Finset.sum_comm]
  conv_rhs at hs =>
    arg 2; arg 2; rw [Finset.sum_comm]
  simp only [β.sum_sq_inner_right] at hs
  exact hs

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

/-- Depth/volume independent on the actual GenK carriers, with its physical grad=n∂. -/
theorem site_graph_bound (f : Site M (n := n)) :
    ‖f‖^2 ≤ 3 * ‖grad M f‖^2 + 2*(n:ℝ)^3 * ‖flatQPrime M f‖^2 := by
  have h := vector_graph_bound n hn (fineTiling M hn) (fun x => f x)
  have hg : ‖grad M f‖^2 = (n:ℝ)^2 *
      ∑ b : Bond (fineExtent M n), ‖f (periodicLatticeShift b.1 b.2)-f b.1‖^2 := by
    rw [← bondEnergy_norm]
    simp only [bondEnergy, grad_apply, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, ← Finset.mul_sum]
  have hq : ‖flatQPrime M f‖^2 = ∑ y ∈ CoarseLattice (fineExtent M n) n,
      ‖(1/(n:ℝ)^3) • ∑ x ∈ blockOf y n, f x‖^2 := by
    rw [norm_sq_coordinates]
    simp only [flatQPrime_block]
    exact (Finset.sum_subtype (CoarseLattice (fineExtent M n) n)
      (fun _ => Iff.rfl) (fun y => ‖(1/(n:ℝ)^3) • ∑ x ∈ blockOf y n, f x‖^2)).symm
  rw [norm_sq_coordinates, hg, hq]
  nlinarith

/-- The cached Δ'_a(1) now has an explicit uniform spectral lower bound. -/
theorem flatDeltaPrime_coercive (k : ℕ) (f : Site M (n := n)) :
    (1/3:ℝ)*‖f‖^2 ≤ (inner ℝ f (flatDeltaPrime M k f) : ℝ) := by
  have h := site_graph_bound M hn f
  have ha := (topWeight_bounds k).1
  have he : (inner ℝ f (flatDeltaPrime M k f) : ℝ) =
      ‖grad M f‖^2 + (topWeight k*(n:ℝ)^3)*‖flatQPrime M f‖^2 := by
    simp only [flatDeltaPrime, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
      siteDelta, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [he]
  have hpos : 0 ≤ (n:ℝ)^3*‖flatQPrime M f‖^2 := by positivity
  nlinarith [mul_nonneg (by linarith : 0 ≤ topWeight k - 3/4) hpos]

/-- Physically normalized coercivity, exactly the form of CMP99b (3.24) for
one whole-torus top stratum at n=2^k. No claim about mixed j-strata. -/
theorem flatDeltaPrime_physical_coercive (k : ℕ) (f : Site M (n := n)) :
    (1/3:ℝ) * ((1/(n:ℝ)^3)*‖f‖^2) ≤
      (1/(n:ℝ)^3)*‖grad M f‖^2 + topWeight k*‖flatQPrime M f‖^2 := by
  have h := mul_le_mul_of_nonneg_left (flatDeltaPrime_coercive M hn k f)
    (by positivity : (0:ℝ) ≤ 1/(n:ℝ)^3)
  rw [flatDeltaPrime_form M k f hn] at h
  nlinarith
end HConstruction.SectBAstra
