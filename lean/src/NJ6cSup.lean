import NJ6bSup

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- **`‖Δ_c A‖ ≤ 8 κ M`** : the printed (124) correction terms, in the sup norm, with NO volume factor. -/
theorem norm_delta124_le_sup {ell : ℕ} (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L 1 ell) (c : CoarseBond L (1 * ell)) (kap M : ℝ) (hkap : 0 ≤ kap) (hM : 0 ≤ M)
    (hE1 : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E1 c u.1‖ ≤ kap)
    (hE2 : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E2 c u.1‖ ≤ kap)
    (hE3 : ‖K.E3 c‖ ≤ kap)
    (A : CoarseBond L 1 → SuTwo) (hA : ∀ b, ‖A b‖ ≤ M) :
    ‖delta124 1 ell V K A c‖ ≤ 8 * kap * M := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellR1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  refine le_trans (norm_delta124_le_terms 1 ell hell V K A c) ?_
  set S := unitSitesOf 1 (1 * ell) c.1.1 with hS
  have hnear : ∀ u ∈ S, ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖ ≤ 3 * ell * M := by
    intro u hu
    refine le_trans (norm_lineIntegral_le 1 V A M hM hA _ _) ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast near_len_le c.1.1 u hu) hM
  have hfar : ∀ u ∈ S, ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖
      ≤ 3 * ell * M := by
    intro u hu
    refine le_trans (norm_lineIntegral_le 1 V A M hM hA _ _) ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast far_len_le c u hu) hM
  have hline : ∀ y, ‖lineIntegral 1 V A y (List.replicate ell c.2)‖ ≤ ell * M := by
    intro y
    refine le_trans (norm_lineIntegral_le 1 V A M hM hA _ _) ?_
    simp
  have hterm : ∀ u ∈ S,
      (‖K.E1 c u.1‖ * ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖
        + ‖K.E1 c u.1‖ * ‖lineIntegral 1 V A u.1 (List.replicate ell c.2)‖
        + ‖K.E2 c u.1‖ * ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖)
      ≤ kap * (7 * ell * M) := by
    intro u hu
    have h1 := mul_le_mul (hE1 u hu) (hnear u hu) (norm_nonneg _) hkap
    have h2 := mul_le_mul (hE1 u hu) (hline u.1) (norm_nonneg _) hkap
    have h3 := mul_le_mul (hE2 u hu) (hfar u hu) (norm_nonneg _) hkap
    nlinarith [h1, h2, h3]
  have hcard : (S.card : ℝ) ≤ (ell : ℝ) ^ 3 := by
    have := unitSitesOf_card_le (L := L) (m := ell) (ell := 1) (by norm_num) c.1.1
      (mem_coarseLattice_one _)
    exact_mod_cast this
  have hsum : (∑ u ∈ S, (‖K.E1 c u.1‖ * ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖
        + ‖K.E1 c u.1‖ * ‖lineIntegral 1 V A u.1 (List.replicate ell c.2)‖
        + ‖K.E2 c u.1‖ * ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖))
      ≤ (ell : ℝ) ^ 3 * (kap * (7 * ell * M)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (kap * (7 * ell * M)) hterm) ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have h3 : (1 / (ell : ℝ) ^ 4) * (∑ u ∈ S, (‖K.E1 c u.1‖ * ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖
        + ‖K.E1 c u.1‖ * ‖lineIntegral 1 V A u.1 (List.replicate ell c.2)‖
        + ‖K.E2 c u.1‖ * ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖))
      ≤ 7 * kap * M := by
    calc _ ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) ^ 3 * (kap * (7 * ell * M))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 7 * kap * M := by field_simp
  have h5 : (1 / (ell : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral 1 V A c.1.1 (List.replicate ell c.2)‖)
      ≤ kap * M := by
    calc _ ≤ (1 / (ell : ℝ)) * (kap * (ell * M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hE3 (hline _) (norm_nonneg _) hkap) (by positivity)
      _ = kap * M := by field_simp
  linarith [h3, h5]

#print axioms norm_delta124_le_sup

end AdalyFormal.NonflatJet
