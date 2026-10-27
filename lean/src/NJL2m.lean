import NJL2k

/-!
# NJL2m -- VOLUME-FREE `L²` BOUND for the (124) correction `Δ`  (stride 1, block `ell`):
`Σ_c ‖(Δ A)(c)‖² ≤ 240 κ² Σ_b ‖A_b‖²`  when every `E_i` has operator norm `≤ κ`.   (`‖Δ‖_{2→2} ≤ √240 κ < 15.5 κ`.)
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

theorem delta124_l2 {ell : ℕ} (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L 1 ell) (kap : ℝ) (hkap : 0 ≤ kap)
    (hE1 : ∀ c : CoarseBond L (1 * ell), ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E1 c u.1‖ ≤ kap)
    (hE2 : ∀ c : CoarseBond L (1 * ell), ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E2 c u.1‖ ≤ kap)
    (hE3 : ∀ c : CoarseBond L (1 * ell), ‖K.E3 c‖ ≤ kap) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), ‖delta124 1 ell V K A c‖ ^ 2
      ≤ 240 * kap ^ 2 * l1 (gA A) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  -- the constants
  have c1 : ((3 * (ell : ℝ)) / (ell : ℝ) ^ 5) * (3 * (ell : ℝ) ^ 3 * (3 * ell) * l1 (gA A)) = 27 * l1 (gA A) := by
    field_simp; ring
  have c2 : ((ell : ℝ) / (ell : ℝ) ^ 5) * (3 * (ell : ℝ) ^ 3 * ell * l1 (gA A)) = 3 * l1 (gA A) := by
    field_simp
  -- the four family sums
  have s1 : ∑ c : CoarseBond L (1 * ell),
      ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N1 ell A c u.1) ^ 2 ≤ 27 * l1 (gA A) := by
    have h := sum_family hell A (3 * ell) (fun _ _ => 0) (fun d _ => stair d)
      (fun d hd _ => stair_length_le d hd)
    simp only [add_zero] at h
    push_cast at h
    exact h.trans (le_of_eq c1)
  have s2 : ∑ c : CoarseBond L (1 * ell),
      ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1) ^ 2 ≤ 3 * l1 (gA A) := by
    have h := sum_family hell A ell (fun d _ => d) (fun _ μ => List.replicate ell μ)
      (fun _ _ μ => by simp)
    exact h.trans (le_of_eq c2)
  have s3 : ∑ c : CoarseBond L (1 * ell),
      ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N3 ell A c u.1) ^ 2 ≤ 27 * l1 (gA A) := by
    have h := sum_family hell A (3 * ell) (fun _ μ => (ell * 1) • Pi.single μ 1) (fun d _ => stair d)
      (fun d hd _ => stair_length_le d hd)
    push_cast at h
    exact h.trans (le_of_eq c1)
  have s4 := sum_cterm hell A
  -- row-wise
  have hrow : ∀ c : CoarseBond L (1 * ell), ‖delta124 1 ell V K A c‖ ^ 2 ≤ 4 * kap ^ 2 *
      ( ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N1 ell A c u.1) ^ 2
      + ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1) ^ 2
      + ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N3 ell A c u.1) ^ 2
      + ((1 / (ell : ℝ)) * N4 ell A c) ^ 2) := by
    intro c
    have hp := delta_pointwise hell V K c kap hkap (hE1 c) (hE2 c) (hE3 c) A
    have hsum : (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        (N1 ell A c u.1 + N2 ell A c u.1 + N3 ell A c u.1)
        = (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N1 ell A c u.1
          + (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1
          + (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N3 ell A c u.1 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
    rw [hsum] at hp
    generalize (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N1 ell A c u.1 = x1 at hp ⊢
    generalize (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1 = x2 at hp ⊢
    generalize (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N3 ell A c u.1 = x3 at hp ⊢
    generalize (1 / (ell : ℝ)) * N4 ell A c = x4 at hp ⊢
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
    refine le_trans hsq ?_
    rw [mul_pow]
    have : (x1 + x2 + x3 + x4) ^ 2 ≤ 4 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4), sq_nonneg (x2 - x3),
        sq_nonneg (x2 - x4), sq_nonneg (x3 - x4)]
    calc kap ^ 2 * (x1 + x2 + x3 + x4) ^ 2 ≤ kap ^ 2 * (4 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg kap)
      _ = 4 * kap ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum (fun c _ => hrow c)) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h4k : 0 ≤ 4 * kap ^ 2 := by positivity
  calc 4 * kap ^ 2 * (_ + _ + _ + _)
      ≤ 4 * kap ^ 2 * (27 * l1 (gA A) + 3 * l1 (gA A) + 27 * l1 (gA A) + 3 * l1 (gA A)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add s1 s2) s3) s4) h4k
    _ = 240 * kap ^ 2 * l1 (gA A) := by ring

#print axioms delta124_l2

end AdalyFormal.NonflatJet
