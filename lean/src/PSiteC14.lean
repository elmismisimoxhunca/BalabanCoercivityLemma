import PSiteC13
import SectBMean

/-!
# SiteC14 -- the PER-BLOCK Neumann/mean Poincaré inequality with in-block bonds:
`Σ_{x ∈ B(y,n)} ‖f x‖² ≤ 3n² Σ_{b ⊂ B(y,n)} ‖f(b₊) − f(b₋)‖² + 2n³ ‖n⁻³ Σ_{x∈B(y,n)} f x‖²`  (scalar and `su(2)`-valued).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice Bond)
open AdalyFormal.Balaban.PoincareBridge
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open HConstruction.SectBAstra (cube_with_mean)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the bonds with BOTH endpoints in the block -/
noncomputable def inBlockBonds (y : PeriodicLatticeSite L) (n : ℕ) : Finset (Bond L) :=
  Finset.univ.filter (fun b => b.1 ∈ blockOf y n ∧ periodicLatticeShift b.1 b.2 ∈ blockOf y n)

theorem mem_inBlockBonds {y : PeriodicLatticeSite L} {n : ℕ} {b : Bond L} :
    b ∈ inBlockBonds y n ↔ b.1 ∈ blockOf y n ∧ periodicLatticeShift b.1 b.2 ∈ blockOf y n := by
  simp [inBlockBonds]

theorem inBlockBonds_disjoint {y y' : PeriodicLatticeSite L} {n n' : ℕ}
    (h : Disjoint (blockOf y n) (blockOf y' n')) : Disjoint (inBlockBonds y n) (inBlockBonds y' n') := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  rw [mem_inBlockBonds] at hb hb'
  exact Finset.disjoint_left.mp h hb.1 hb'.1

theorem block_energy_le_inBlock {y : PeriodicLatticeSite L} {n : ℕ}
    (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (lam : PeriodicLatticeSite L → ℝ) :
    cE0 n (fun p => lam (chart y n p)) + cE1 n (fun p => lam (chart y n p))
        + cE2 n (fun p => lam (chart y n p))
      ≤ ∑ b ∈ inBlockBonds y n, (AdalyFormal.Balaban.LatticeOperators.gradValue lam b) ^ 2 := by
  classical
  let T0 : Finset (Bond L) := Finset.univ.image (fun j : StepIdx n => (chart y n (cubeOf0 j), (0 : Fin 3)))
  let T1 : Finset (Bond L) := Finset.univ.image (fun j : StepIdx n => (chart y n (cubeOf1 j), (1 : Fin 3)))
  let T2 : Finset (Bond L) := Finset.univ.image (fun j : StepIdx n => (chart y n (cubeOf2 j), (2 : Fin 3)))
  have e0 : cE0 n (fun p => lam (chart y n p))
      = ∑ b ∈ T0, (AdalyFormal.Balaban.LatticeOperators.gradValue lam b) ^ 2 := by
    rw [cE0_eq_stepIdx]
    simp only [T0]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [AdalyFormal.Balaban.LatticeOperators.gradValue]
      rw [← chart_step0 hfit j]
    · intro j _ j' _ h
      exact cubeOf0_injective (chart_injective hfit (Prod.ext_iff.mp h).1)
  have e1 : cE1 n (fun p => lam (chart y n p))
      = ∑ b ∈ T1, (AdalyFormal.Balaban.LatticeOperators.gradValue lam b) ^ 2 := by
    rw [cE1_eq_stepIdx]
    simp only [T1]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [AdalyFormal.Balaban.LatticeOperators.gradValue]
      rw [← chart_step1 hfit j]
    · intro j _ j' _ h
      exact cubeOf1_injective (chart_injective hfit (Prod.ext_iff.mp h).1)
  have e2 : cE2 n (fun p => lam (chart y n p))
      = ∑ b ∈ T2, (AdalyFormal.Balaban.LatticeOperators.gradValue lam b) ^ 2 := by
    rw [cE2_eq_stepIdx]
    simp only [T2]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [AdalyFormal.Balaban.LatticeOperators.gradValue]
      rw [← chart_step2 hfit j]
    · intro j _ j' _ h
      exact cubeOf2_injective (chart_injective hfit (Prod.ext_iff.mp h).1)
  rw [e0, e1, e2]
  have d01 : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]; intro b hb hb'
    simp only [T0, T1, Finset.mem_image] at hb hb'
    obtain ⟨j, _, rfl⟩ := hb; obtain ⟨j', _, h⟩ := hb'
    have := (Prod.ext_iff.mp h).2; simp at this
  have d02 : Disjoint T0 T2 := by
    rw [Finset.disjoint_left]; intro b hb hb'
    simp only [T0, T2, Finset.mem_image] at hb hb'
    obtain ⟨j, _, rfl⟩ := hb; obtain ⟨j', _, h⟩ := hb'
    have := (Prod.ext_iff.mp h).2; simp at this
  have d12 : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]; intro b hb hb'
    simp only [T1, T2, Finset.mem_image] at hb hb'
    obtain ⟨j, _, rfl⟩ := hb; obtain ⟨j', _, h⟩ := hb'
    have := (Prod.ext_iff.mp h).2; simp at this
  have hd : Disjoint (T0 ∪ T1) T2 := Finset.disjoint_union_left.mpr ⟨d02, d12⟩
  rw [← Finset.sum_union d01, ← Finset.sum_union hd]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => sq_nonneg _)
  intro b hb
  simp only [Finset.mem_union, T0, T1, T2, Finset.mem_image, Finset.mem_univ, true_and] at hb
  rw [mem_inBlockBonds]
  rcases hb with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩
  · exact ⟨chart_mem_block hfit _, by rw [← chart_step0 hfit j]; exact chart_mem_block hfit _⟩
  · exact ⟨chart_mem_block hfit _, by rw [← chart_step1 hfit j]; exact chart_mem_block hfit _⟩
  · exact ⟨chart_mem_block hfit _, by rw [← chart_step2 hfit j]; exact chart_mem_block hfit _⟩


theorem block_poincare_scalar {y : PeriodicLatticeSite L} {n : ℕ} (hn : 0 < n)
    (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (f : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ blockOf y n, (f x) ^ 2 ≤
      3 * (n : ℝ) ^ 2 * ∑ b ∈ inBlockBonds y n, (AdalyFormal.Balaban.LatticeOperators.gradValue f b) ^ 2
        + 2 * (n : ℝ) ^ 3 * ((1 / (n : ℝ) ^ 3) * ∑ x ∈ blockOf y n, f x) ^ 2 := by
  have h := cube_with_mean n hn (fun p => f (chart y n p))
  have h1 := block_energy_le_inBlock hfit f
  have hn2 : (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 hn2
  rw [sum_block_eq_cube hfit, sum_block_eq_cube hfit (fun x => f x)]
  unfold cSumSq at h
  linarith

theorem block_poincare_vector {y : PeriodicLatticeSite L} {n : ℕ} (hn : 0 < n)
    (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (f : PeriodicLatticeSite L → SuTwo) :
    ∑ x ∈ blockOf y n, ‖f x‖ ^ 2 ≤
      3 * (n : ℝ) ^ 2 * ∑ b ∈ inBlockBonds y n, ‖f (periodicLatticeShift b.1 b.2) - f b.1‖ ^ 2
        + 2 * (n : ℝ) ^ 3 * ‖(1 / (n : ℝ) ^ 3) • ∑ x ∈ blockOf y n, f x‖ ^ 2 := by
  let β := stdOrthonormalBasis ℝ SuTwo
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    block_poincare_scalar hn hfit (fun x => inner ℝ (β i) (f x)))
  have hg (i : Fin (Module.finrank ℝ SuTwo)) (b : Bond L) :
      AdalyFormal.Balaban.LatticeOperators.gradValue (fun x => inner ℝ (β i) (f x)) b =
        inner ℝ (β i) (f (periodicLatticeShift b.1 b.2) - f b.1) := by
    simp only [AdalyFormal.Balaban.LatticeOperators.gradValue, inner_sub_right]
  have hq (i : Fin (Module.finrank ℝ SuTwo)) :
      (1 / (n : ℝ) ^ 3) * ∑ x ∈ blockOf y n, inner ℝ (β i) (f x) =
        inner ℝ (β i) ((1 / (n : ℝ) ^ 3) • ∑ x ∈ blockOf y n, f x) := by
    simp only [inner_smul_right, inner_sum]
  simp only [hg, hq] at hs
  rw [Finset.sum_comm] at hs
  simp only [β.sum_sq_inner_right] at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  conv_rhs at hs =>
    arg 1; arg 2; rw [Finset.sum_comm]
  simp only [β.sum_sq_inner_right] at hs
  exact hs

end AdalyFormal.SiteCoercivity
