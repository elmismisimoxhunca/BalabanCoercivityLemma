import SectBInverse
import AdalyFormal.Balaban.PoincareBridge
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HConstruction.SectBAstra
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.PoincareBridge
open HConstruction.SectBBase

/-- Center only INSIDE each Neumann cube. Never differentiate a discontinuous
block-constant extension across block boundaries. -/
theorem cube_with_mean (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ) :
    cSumSq n f ≤ 3 * (n:ℝ)^2 * (cE0 n f + cE1 n f + cE2 n f) +
      2 * (n:ℝ)^3 * ((1/(n:ℝ)^3) * ∑ p, f p)^2 := by
  let m : ℝ := (1/(n:ℝ)^3) * ∑ p, f p
  let h : Cube n → ℝ := fun p => f p - m
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc : (Fintype.card (Cube n) : ℝ) = (n:ℝ)^3 := by
    simp [Cube, Fintype.card_prod, pow_succ]; ring
  have hz : ∑ p, h p = 0 := by
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hc]
    dsimp [m]
    field_simp
    ring
  have he0 : cE0 n h = cE0 n f := by
    simp only [cE0_eq_stepIdx, h, sub_sub_sub_cancel_right]
  have he1 : cE1 n h = cE1 n f := by
    simp only [cE1_eq_stepIdx, h, sub_sub_sub_cancel_right]
  have he2 : cE2 n h = cE2 n f := by
    simp only [cE2_eq_stepIdx, h, sub_sub_sub_cancel_right]
  have hp := cube_poincare n (by omega) h hz
  rw [he0, he1, he2] at hp
  have hs : cSumSq n f ≤ 2*cSumSq n h + 2*(n:ℝ)^3*m^2 := by
    have hh : ∀ p, (f p)^2 ≤ 2*(h p)^2+2*m^2 := by
      intro p; dsimp [h]; nlinarith [sq_nonneg (f p - 2*m)]
    calc cSumSq n f ≤ ∑ p, (2*(h p)^2+2*m^2) :=
        Finset.sum_le_sum (fun p _ => hh p)
      _ = _ := by
        simp only [cSumSq, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
        ring
  have he := add_nonneg (add_nonneg (cE0_nonneg n f) (cE1_nonneg n f)) (cE2_nonneg n f)
  have hcoef : 3*(n:ℝ)*((n:ℝ)-1) * (cE0 n f + cE1 n f + cE2 n f) ≤
      3*(n:ℝ)^2*(cE0 n f + cE1 n f + cE2 n f) := by
    apply mul_le_mul_of_nonneg_right _ he
    nlinarith
  change _ ≤ _ + 2*(n:ℝ)^3*m^2
  nlinarith

/-- The nonzero-mean scalar block estimate on the literal periodic site graph. -/
theorem scalar_graph_bound {L : PeriodicLatticeExtent} (n : ℕ) (hn : 0 < n)
    (hdvd : ∀ μ, n ∣ L μ+1) (f : PeriodicLatticeSite L → ℝ) :
    ∑ x, (f x)^2 ≤ 3*(n:ℝ)^2 *
      ∑ b : Bond L, (AdalyFormal.Balaban.LatticeOperators.gradValue f b)^2 +
      2*(n:ℝ)^3 * ∑ y ∈ CoarseLattice L n,
        ((1/(n:ℝ)^3) * ∑ x ∈ blockOf y n, f x)^2 := by
  have hp : ∀ y ∈ CoarseLattice L n,
      ∑ x ∈ blockOf y n, (f x)^2 ≤
      3*(n:ℝ)^2 * (cE0 n (fun p => f (chart y n p)) +
        cE1 n (fun p => f (chart y n p)) + cE2 n (fun p => f (chart y n p))) +
      2*(n:ℝ)^3 * ((1/(n:ℝ)^3) * ∑ x ∈ blockOf y n, f x)^2 := by
    intro y hy
    rw [sum_block_eq_cube (coarseLattice_fits hdvd hy),
      sum_block_eq_cube (coarseLattice_fits hdvd hy)]
    exact cube_with_mean n hn _
  have hs := Finset.sum_le_sum hp
  rw [← sum_eq_blocks n hn hdvd, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have he := block_energy_sum_le f n hdvd
  have he' := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 3*(n:ℝ)^2)
  linarith

/-- The printed a_j recurrence has a uniform positive lower endpoint. -/
theorem weightIter_bounds (j : ℕ) : (3/4:ℝ) ≤ weightIter j ∧ weightIter j ≤ 1 := by
  induction j with
  | zero => norm_num [weightIter]
  | succ j ih =>
    have hd : 0 < 1/4 + weightIter j := by linarith [ih.1]
    simp only [weightIter]
    constructor
    · apply (le_div_iff₀ hd).mpr; nlinarith [ih.1]
    · apply (div_le_iff₀ hd).mpr; linarith

theorem topWeight_bounds (k : ℕ) : (3/4:ℝ) ≤ topWeight k ∧ topWeight k ≤ 1 :=
  weightIter_bounds _

end HConstruction.SectBAstra
