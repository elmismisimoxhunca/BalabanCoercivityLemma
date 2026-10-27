import SectBPath
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK HConstruction.SectBBase
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.PoincareBridge (sum_eq_blocks)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

/-- Jensen/Cauchy–Schwarz per actual n³-block, with no coarse-volume factor. -/
theorem qDrift_block_sq (U : Links M (n := n)) (α : ℝ)
    (hsmall : frobSupBond U ≤ α/(n:ℝ)) (f : Site M (n := n))
    (y : Centers M (n := n)) :
    ‖qDrift M U f y‖^2 ≤ 36*α^2*(1/(n:ℝ)^3)*
      ∑ x ∈ blockOf y.1 n, ‖f x‖^2 := by
  have h0 := qDrift_block_small M hn U α hsmall y f
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hs := sq_sum_le_card_mul_sum_sq
    (s := blockOf y.1 n) (f := fun x => 6*α*‖f x‖)
  rw [card_blockOf_of_coarse (fineTiling M hn) y.2] at hs
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  calc
    ‖qDrift M U f y‖^2 ≤ ((1/(n:ℝ)^3)*∑ x ∈ blockOf y.1 n, 6*α*‖f x‖)^2 := hsq
    _ = (1/(n:ℝ)^6)*(∑ x ∈ blockOf y.1 n, 6*α*‖f x‖)^2 := by ring
    _ ≤ (1/(n:ℝ)^6)*((n:ℝ)^3 * ∑ x ∈ blockOf y.1 n, (6*α*‖f x‖)^2) := by
      gcongr
      simpa only [Nat.cast_pow] using hs
    _ = 36*α^2*(1/(n:ℝ)^3)*∑ x ∈ blockOf y.1 n, ‖f x‖^2 := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      field_simp
      ring

/-- A2's actual global operator drift with the required n^-3/2 factor. -/
theorem qDrift_sq (U : Links M (n := n)) (α : ℝ)
    (hsmall : frobSupBond U ≤ α/(n:ℝ)) (f : Site M (n := n)) :
    ‖qDrift M U f‖^2 ≤ 36*α^2*(1/(n:ℝ)^3)*‖f‖^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => qDrift_block_sq M hn U α hsmall f y)
  rw [← norm_sq_coordinates (qDrift M U f)] at h
  simp only [← Finset.mul_sum] at h
  have hblocks : (∑ y : Centers M (n := n), ∑ x ∈ blockOf y.1 n, ‖f x‖^2) =
      ∑ x : PeriodicLatticeSite (fineExtent M n), ‖f x‖^2 := by
    rw [sum_eq_blocks n hn (fineTiling M hn)]
    exact (Finset.sum_subtype (CoarseLattice (fineExtent M n) n)
      (fun _ => Iff.rfl) (fun y => ∑ x ∈ blockOf y n, ‖f x‖^2)).symm
  rw [hblocks, ← norm_sq_coordinates f] at h
  exact h
end HConstruction.SectBP1
