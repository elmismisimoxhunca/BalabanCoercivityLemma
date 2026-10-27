import NJL2g

/-!
# NJL2h -- pointwise bound of `‖Δ_c A‖` by the four absolute path sums.
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
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QOne (pathSite)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem delta_pointwise {ell : ℕ} (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L 1 ell) (c : CoarseBond L (1 * ell)) (kap : ℝ) (hkap : 0 ≤ kap)
    (hE1 : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E1 c u.1‖ ≤ kap)
    (hE2 : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ‖K.E2 c u.1‖ ≤ kap)
    (hE3 : ‖K.E3 c‖ ≤ kap) (A : CoarseBond L 1 → SuTwo) :
    ‖delta124 1 ell V K A c‖
      ≤ kap * ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
            (N1 ell A c u.1 + N2 ell A c u.1 + N3 ell A c u.1) + (1 / (ell : ℝ)) * N4 ell A c) := by
  refine le_trans (norm_delta124_le_terms 1 ell hell V K A c) ?_
  have hnear : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
      ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖ ≤ N1 ell A c u.1 := by
    intro u _
    rw [coarseGammaPath_one_eq_stair]
    exact norm_lineIntegral_le_pathSum V A _ c.1.1
  have hline : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
      ‖lineIntegral 1 V A u.1 (List.replicate ell c.2)‖ ≤ N2 ell A c u.1 := by
    intro u _
    have := norm_lineIntegral_le_pathSum V A (List.replicate ell c.2) u.1
    unfold N2
    rwa [add_sub_cancel]
  have hfar : ∀ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
      ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖
        ≤ N3 ell A c u.1 := by
    intro u _
    have e1 : partner c u.1 - cPlus c = u.1 - c.1.1 := partner_sub_cPlus u.1 c.1.1 c.2 (ell * 1)
    have e2 : cPlus c = c.1.1 + (ell * 1) • Pi.single c.2 1 := pathSite_eq_add c.1.1 c.2 (ell * 1)
    rw [coarseGammaPath_one_eq_stair, e1]
    unfold N3
    rw [← e2]
    exact norm_lineIntegral_le_pathSum V A _ (cPlus c)
  have hc : ‖lineIntegral 1 V A c.1.1 (List.replicate ell c.2)‖ ≤ N4 ell A c :=
    norm_lineIntegral_le_pathSum V A (List.replicate ell c.2) c.1.1
  have h4 : (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        (‖K.E1 c u.1‖ * ‖lineIntegral 1 V A c.1.1 (coarseGammaPath 1 c.1.1 u.1)‖
         + ‖K.E1 c u.1‖ * ‖lineIntegral 1 V A u.1 (List.replicate ell c.2)‖
         + ‖K.E2 c u.1‖ * ‖lineIntegral 1 V A (cPlus c) (coarseGammaPath 1 (cPlus c) (partner c u.1))‖)
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1,
        kap * (N1 ell A c u.1 + N2 ell A c u.1 + N3 ell A c u.1) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u hu => ?_)) (by positivity)
    have a1 := mul_le_mul (hE1 u hu) (hnear u hu) (norm_nonneg _) hkap
    have a2 := mul_le_mul (hE1 u hu) (hline u hu) (norm_nonneg _) hkap
    have a3 := mul_le_mul (hE2 u hu) (hfar u hu) (norm_nonneg _) hkap
    nlinarith [a1, a2, a3]
  have h5 : (1 / (ell : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral 1 V A c.1.1 (List.replicate ell c.2)‖)
      ≤ (1 / (ell : ℝ)) * (kap * N4 ell A c) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hE3 hc (norm_nonneg _) hkap) (by positivity)
  rw [← Finset.mul_sum] at h4
  nlinarith [h4, h5]

#print axioms delta_pointwise

end AdalyFormal.NonflatJet
