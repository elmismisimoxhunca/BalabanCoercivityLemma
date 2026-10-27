import NJL2h

/-!
# NJL2i -- the four row-wise square bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- `((1/ell⁴) Σ_S N)² ≤ (m/ell⁵) Σ_S P` when `N² ≤ m P` termwise and `|S| ≤ ell³`. -/
theorem cs_block {ι : Type*} {ell : ℕ} (hell : 0 < ell) (S : Finset ι) (hS : (S.card : ℝ) ≤ (ell : ℝ) ^ 3)
    (N P : ι → ℝ) (m : ℝ) (hm : 0 ≤ m) (hN : ∀ i ∈ S, N i ^ 2 ≤ m * P i) (hP : ∀ i, 0 ≤ P i) :
    ((1 / (ell : ℝ) ^ 4) * ∑ i ∈ S, N i) ^ 2 ≤ (m / (ell : ℝ) ^ 5) * ∑ i ∈ S, P i := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have h1 : (∑ i ∈ S, N i) ^ 2 ≤ S.card * ∑ i ∈ S, N i ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ i ∈ S, N i ^ 2 ≤ ∑ i ∈ S, m * P i := Finset.sum_le_sum hN
  rw [← Finset.mul_sum] at h2
  have hPs : 0 ≤ ∑ i ∈ S, P i := Finset.sum_nonneg (fun i _ => hP i)
  have h3 : (∑ i ∈ S, N i) ^ 2 ≤ (ell : ℝ) ^ 3 * (m * ∑ i ∈ S, P i) :=
    le_trans h1 (mul_le_mul hS h2 (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by positivity))
  calc ((1 / (ell : ℝ) ^ 4) * ∑ i ∈ S, N i) ^ 2
      = (1 / (ell : ℝ) ^ 8) * (∑ i ∈ S, N i) ^ 2 := by field_simp
    _ ≤ (1 / (ell : ℝ) ^ 8) * ((ell : ℝ) ^ 3 * (m * ∑ i ∈ S, P i)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (m / (ell : ℝ) ^ 5) * ∑ i ∈ S, P i := by field_simp

theorem stair_length_le {ell : ℕ} (d : PeriodicLatticeSite L) (hd : d ∈ Doff L ell) :
    (stair d).length ≤ 3 * ell := by
  simp only [Doff, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  have h0 := hd 0; have h1 := hd 1; have h2 := hd 2
  simp only [stair, List.length_append, List.length_replicate]
  omega

#print axioms cs_block
#print axioms stair_length_le

end AdalyFormal.NonflatJet
