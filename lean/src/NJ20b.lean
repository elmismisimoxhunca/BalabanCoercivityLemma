import NJ20a

/-!
# NJ20b -- `L²` main-term drift: `Σ_c ‖(T1(V)-T1(1))A(c)‖² ≤ 192 ell² ε₀² ‖A‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathHolonomy coarseTransportPath
  coarsePathHolonomy_trivialU unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm norm_RMap_sub_self_le)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem T1_drift_term {ell : ℕ} (V : PeriodicLinkConfiguration SU2 L)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell))
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1}) (hu : u ∈ unitSitesOf 1 (1 * ell) c.1.1) :
    ‖(∑ i ∈ Finset.range ell,
          if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
            RMap (coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i))
              (A (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2)) else 0)
        - ∑ i ∈ Finset.range ell,
          if h : pathSite u.1 c.2 (i * 1) ∈ CoarseLattice L 1 then
            RMap (coarsePathHolonomy 1 (trivialU L) c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i))
              (A (⟨pathSite u.1 c.2 (i * 1), h⟩, c.2)) else 0‖
      ≤ 8 * ell * ε0 * N2 ell A c u.1 := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hN2 : N2 ell A c u.1 = ∑ i ∈ Finset.range ell, ‖A (⟨pathSite u.1 c.2 i, mem_coarseLattice_one _⟩, c.2)‖ := by
    unfold N2
    rw [add_sub_cancel, pathSum_rep]
    rfl
  rw [hN2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi' : i < ell := Finset.mem_range.mp hi
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
  have hmul : 2 * frobNorm (((coarsePathHolonomy 1 V c.1.1 (coarseTransportPath 1 c.1.1 u.1 c.2 i) : SU2) : M2) - 1)
      ≤ 8 * ell * ε0 := by linarith
  have hnn := norm_nonneg (A (⟨pathSite u.1 c.2 (i * 1), mem_coarseLattice_one _⟩, c.2))
  calc _ ≤ (8 * ell * ε0) * ‖A (⟨pathSite u.1 c.2 (i * 1), mem_coarseLattice_one _⟩, c.2)‖ :=
        mul_le_mul_of_nonneg_right hmul hnn
    _ = _ := by rw [Nat.mul_one]

theorem T1_drift_row {ell : ℕ} (hell : 0 < ell) (V : PeriodicLinkConfiguration SU2 L)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0)
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell)) :
    ‖unitToCoarseCov 1 ell V A c - unitToCoarseCov 1 ell (trivialU L) A c‖
      ≤ 8 * ell * ε0 * ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, N2 ell A c u.1) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have h14 : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 4 := by positivity
  unfold unitToCoarseCov
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h14, ← Finset.sum_sub_distrib]
  calc _ ≤ (1 / (ell : ℝ) ^ 4) * ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, (8 * ell * ε0 * N2 ell A c u.1) := by
        refine mul_le_mul_of_nonneg_left ?_ h14
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun u hu => ?_))
        exact T1_drift_term V ε0 hε0 hV A c u hu
    _ = _ := by rw [← Finset.mul_sum]; ring

#print axioms T1_drift_row

end AdalyFormal.NonflatJet
