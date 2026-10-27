import NJ5Path

/-!
# NJ6Delta -- volume-free sup-norm bound of the (124) correction `Δ = term2 + term3 + term4 + term5` (stride 1, block `ell`):
`‖Δ_c A‖ ≤ 8 κ M` when every `E_i` has norm `≤ κ` and every bond value of `A` has norm `≤ M`.
(The count: three block sums `≤ ell^3 · κ · (3(ell-1) + ell + 3(ell-1)) M / ell^4 ≤ 7κM`, plus `κ M` from `E3`.)
-/
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
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

/-- the exact term-wise bound (stage `OneStep124.norm_delta124_le`, re-derived here). -/
theorem norm_delta124_le_terms (ell m : ℕ) (hm : 0 < m)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : Coeff124 L ell m) (A : CoarseBond L ell → SuTwo) (c : CoarseBond L (ell * m)) :
    ‖delta124 ell m V K A c‖
      ≤ (1 / (m : ℝ) ^ 4) *
          (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
            (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
             + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
             + ‖K.E2 c u.1‖ *
                 ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1))‖))
        + (1 / (m : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖) := by
  have hpos4 : (0 : ℝ) ≤ 1 / (m : ℝ) ^ 4 := by positivity
  have hpos1 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hsum :
      ‖term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c‖
        ≤ (1 / (m : ℝ) ^ 4) *
          (∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
            (‖K.E1 c u.1‖ * ‖lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1)‖
             + ‖K.E1 c u.1‖ * ‖lineIntegral ell V A u.1 (List.replicate m c.2)‖
             + ‖K.E2 c u.1‖ *
                 ‖lineIntegral ell V A (cPlus c) (coarseGammaPath ell (cPlus c) (partner c u.1))‖)) := by
    have hcollapse :
        term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c
          = (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell (ell * m) c.1.1,
              (K.E1 c u.1 (lineIntegral ell V A c.1.1 (coarseGammaPath ell c.1.1 u.1))
               + K.E1 c u.1
                   (RMap (AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy ell V c.1.1
                       (coarseGammaPath ell c.1.1 u.1))
                     (lineIntegral ell V A u.1 (List.replicate m c.2)))
               - K.E2 c u.1
                   (RMap (K.gbar c)
                     (lineIntegral ell V A (cPlus c)
                       (coarseGammaPath ell (cPlus c) (partner c u.1))))) := by
      simp only [term2, term3, term4]
      rw [← smul_add, ← smul_neg, ← smul_add, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
      abel
    rw [hcollapse, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos4]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _) ?_) hpos4
    refine Finset.sum_le_sum fun u _ => ?_
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_
    · exact (K.E1 c u.1).le_opNorm _
    · calc _ ≤ ‖K.E1 c u.1‖ * ‖RMap (AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy ell V c.1.1
              (coarseGammaPath ell c.1.1 u.1)) (lineIntegral ell V A u.1 (List.replicate m c.2))‖ :=
            (K.E1 c u.1).le_opNorm _
        _ = _ := by rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    · calc _ ≤ ‖K.E2 c u.1‖ * ‖RMap (K.gbar c) (lineIntegral ell V A (cPlus c)
              (coarseGammaPath ell (cPlus c) (partner c u.1)))‖ := (K.E2 c u.1).le_opNorm _
        _ = _ := by rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
  have hterm5 : ‖term5 ell m V K A c‖
      ≤ (1 / (m : ℝ)) * (‖K.E3 c‖ * ‖lineIntegral ell V A c.1.1 (List.replicate m c.2)‖) := by
    rw [term5, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos1]
    exact mul_le_mul_of_nonneg_left ((K.E3 c).le_opNorm _) hpos1
  have hdelta : delta124 ell m V K A c
      = (term2 ell m V K A c + term3 ell m V K A c + term4 ell m V K A c)
        + term5 ell m V K A c := by
    simp only [delta124]
  rw [hdelta]
  exact le_trans (norm_add_le _ _) (add_le_add hsum hterm5)

#print axioms norm_delta124_le_terms

end AdalyFormal.NonflatJet
