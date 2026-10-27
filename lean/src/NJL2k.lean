import NJL2j

/-!
# NJL2k -- VOLUME-FREE `L²` BOUND for the (124) correction:  `Σ_c ‖Δ_c A‖² ≤ 240 κ² Σ_b ‖A_b‖²`.
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

theorem sum_cterm {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), ((1 / (ell : ℝ)) * N4 ell A c) ^ 2 ≤ 3 * l1 (gA A) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hrow : ∀ c : CoarseBond L (1 * ell), ((1 / (ell : ℝ)) * N4 ell A c) ^ 2
      ≤ (1 / (ell : ℝ)) * pathSum (gA A) c.1.1 (List.replicate ell c.2) := by
    intro c
    have h := pathSum_sq_le (fA A) c.1.1 (List.replicate ell c.2)
    rw [List.length_replicate] at h
    have hnn := pathSum_nonneg (gA A) (gA_nonneg A) c.1.1 (List.replicate ell c.2)
    unfold N4
    calc ((1 / (ell : ℝ)) * pathSum (fA A) c.1.1 (List.replicate ell c.2)) ^ 2
        = (1 / (ell : ℝ)) ^ 2 * (pathSum (fA A) c.1.1 (List.replicate ell c.2)) ^ 2 := by ring
      _ ≤ (1 / (ell : ℝ)) ^ 2 * (ell * pathSum (gA A) c.1.1 (List.replicate ell c.2)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (1 / (ell : ℝ)) * pathSum (gA A) c.1.1 (List.replicate ell c.2) := by field_simp
  refine le_trans (Finset.sum_le_sum (fun c _ => hrow c)) ?_
  rw [← Finset.mul_sum]
  have h1 := sum_rows_le (n := 1 * ell) (fun y μ => pathSum (gA A) y (List.replicate ell μ))
    (fun y μ => pathSum_nonneg _ (gA_nonneg A) _ _)
  have h2 : ∀ μ : Fin 3, ∑ y : PeriodicLatticeSite L, pathSum (gA A) y (List.replicate ell μ)
      ≤ ell * l1 (gA A) := by
    intro μ
    have := sum_pathSum_translate (gA A) (gA_nonneg A) 0 (List.replicate ell μ)
    simpa only [add_zero, List.length_replicate] using this
  have h3 : ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, pathSum (gA A) y (List.replicate ell μ)
      ≤ 3 * (ell * l1 (gA A)) := by
    refine le_trans (Finset.sum_le_sum (fun μ _ => h2 μ)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; rfl
  calc (1 / (ell : ℝ)) * ∑ c : CoarseBond L (1 * ell), pathSum (gA A) c.1.1 (List.replicate ell c.2)
      ≤ (1 / (ell : ℝ)) * (3 * (ell * l1 (gA A))) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h3) (by positivity)
    _ = 3 * l1 (gA A) := by field_simp

#print axioms sum_cterm

end AdalyFormal.NonflatJet
