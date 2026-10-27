import NJ6cSup

/-!
# NJ7T1 -- sup-norm drift of the covariant main term `T1 = unitToCoarseCov 1 ell V` from the flat one:
`‖(T1(V) - T1(1)) A (c)‖ ≤ 8 ell ε₀ M` when every link is `ε₀`-close to `1` (Frobenius) and every bond value of `A` is `≤ M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathHolonomy coarseTransportPath
  coarsePathHolonomy_trivialU unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm norm_RMap_sub_self_le)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open OneStep124 (unitSitesOf_card_le)
open SmallnessBridge.Assemble (holonomyFactors holonomyFactors_prod holonomyFactors_length mem_holonomyFactors)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem frob_hol_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ)
    (h : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    frobNorm (((coarsePathHolonomy s V y p : SU2) : M2) - 1) ≤ p.length * ε0 := by
  rw [← holonomyFactors_prod]
  have := AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_prod_sub_one_le
    (holonomyFactors s V y p) ε0 (fun g hg => by
      obtain ⟨y', μ, rfl⟩ := mem_holonomyFactors hg
      exact h _)
  rwa [holonomyFactors_length] at this

theorem norm_T1_drift_le {ell : ℕ} (hell : 0 < ell) (V : PeriodicLinkConfiguration SU2 L)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (A : CoarseBond L 1 → SuTwo) (M : ℝ) (hM : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M)
    (c : CoarseBond L (1 * ell)) :
    ‖unitToCoarseCov 1 ell V A c - unitToCoarseCov 1 ell (trivialU L) A c‖ ≤ 8 * ell * ε0 * M := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  unfold unitToCoarseCov
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Finset.sum_sub_distrib]
  set S := unitSitesOf 1 (1 * ell) c.1.1 with hS
  have hterm : ∀ u ∈ S, ‖∑ i ∈ Finset.range ell,
      ((if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
        RMap (coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i))
          (A (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2)) else 0)
       - (if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
        RMap (coarsePathHolonomy 1 (trivialU L) c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i))
          (A (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2)) else 0))‖ ≤ ell * (8 * ell * ε0 * M) := by
    intro u hu
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (8 * ell * ε0 * M) (fun i hi => ?_)) ?_
    · have hi' : i < ell := Finset.mem_range.mp hi
      rw [dif_pos (mem_coarseLattice_one _), dif_pos (mem_coarseLattice_one _),
        coarsePathHolonomy_trivialU, RMap_one]
      refine le_trans (norm_RMap_sub_self_le _ _) ?_
      have hlen : (coarseTransportPath 1 c.1.1 u.1 c.2 i).length ≤ 4 * ell := by
        unfold coarseTransportPath
        rw [List.length_append, List.length_replicate]
        have := near_len_le c.1.1 u hu
        omega
      have hf := frob_hol_le 1 V ε0 hV c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i)
      have hf' : frobNorm (((coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i) : SU2) : M2) - 1)
          ≤ 4 * ell * ε0 :=
        le_trans hf (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hε0)
      have hAb := hA (⟨pathSite u.1 c.2 (i * 1), mem_coarseLattice_one _⟩, c.2)
      calc 2 * frobNorm _ * ‖A _‖ ≤ 2 * (4 * ell * ε0) * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left hf' (by norm_num)) hAb (norm_nonneg _) (by positivity)
        _ = 8 * ell * ε0 * M := by ring
    · simp [nsmul_eq_mul]
  simp only [← Finset.sum_sub_distrib]
  have hcard : (S.card : ℝ) ≤ (ell : ℝ) ^ 3 := by
    have := unitSitesOf_card_le (L := L) (m := ell) (ell := 1) (by norm_num) c.1.1
      (mem_coarseLattice_one _)
    exact_mod_cast this
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _)
    (Finset.sum_le_card_nsmul _ _ _ hterm)) (by positivity)) ?_
  rw [nsmul_eq_mul]
  calc 1 / (ell : ℝ) ^ 4 * ((S.card : ℝ) * (ell * (8 * ell * ε0 * M)))
      ≤ 1 / (ell : ℝ) ^ 4 * ((ell : ℝ) ^ 3 * (ell * (8 * ell * ε0 * M))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) (by positivity)
    _ = 8 * ell * ε0 * M := by field_simp

#print axioms norm_T1_drift_le

end AdalyFormal.NonflatJet
