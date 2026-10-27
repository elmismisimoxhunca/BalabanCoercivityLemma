import DLR69
import BC2

/-!
# DL70 -- the covariant main term `T1 = unitToCoarseCov` in `ℓ¹`, at ANY background

`T1(V)A(c) = ell⁻⁴ Σ_{u ∈ B(c₋)} Σ_{i<ell} RMap(hol)(A(u + i e_μ, μ))` (CMP98 (125)); `RMap` is an isometry
(`FaithfulCoercivitySU2.norm_RMap`), so
* `T1_pointwise_l1` : `‖T1(V)A(c)‖ ≤ ell⁻⁴ Σ_u Σ_i ‖A(u + i e_μ, μ)‖`  — no smallness of `V` needed;
* **`T1_l1`** : `Σ_c ‖T1(V)A(c)‖ ≤ ell⁻³ Σ_b ‖A b‖`  (the counting of BC2 `T1_flat_l2`, copied, with `‖·‖` in place of `‖·‖²`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.NonflatJet (fA fA_nonneg l1)
open AdalyFormal.BondComposite (sum_blocks_le sum_pathSite)

variable {L : PeriodicLatticeExtent}

theorem T1_pointwise_l1 {ell : ℕ} (V : PeriodicLinkConfiguration SU2 L) (A : CoarseBond L 1 → SuTwo)
    (c : CoarseBond L (1 * ell)) :
    ‖unitToCoarseCov 1 ell V A c‖ ≤ (1 / (ell : ℝ) ^ 4) *
      ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, fA A (pathSite u.1 c.2 (i * 1), c.2) := by
  unfold unitToCoarseCov
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [dif_pos (mem_coarseLattice_one _), AdalyFormal.Balaban.FaithfulCoercivitySU2.norm_RMap]
  rfl

/-- the counting behind `T1_l1`, for the majorant itself -/
theorem T1_count {ell : ℕ} (hell : 0 < ell) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), (1 / (ell : ℝ) ^ 4) *
        ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, fA A (pathSite u.1 c.2 (i * 1), c.2)
      ≤ (1 / (ell : ℝ) ^ 3) * l1 (fA A) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hell1 : 0 < 1 * ell := by omega
  rw [← Finset.mul_sum]
  have h2 : ∑ c : CoarseBond L (1 * ell),
        ∑ u ∈ unitSitesOf 1 (1 * ell) c.1.1, ∑ i ∈ Finset.range ell, fA A (pathSite u.1 c.2 (i * 1), c.2)
      ≤ ∑ μ : Fin 3, ∑ i ∈ Finset.range ell, ∑ z : PeriodicLatticeSite L, fA A (z, μ) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun μ _ => ?_
    have hswap : ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
          ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, ∑ i ∈ Finset.range ell, fA A (pathSite u.1 μ (i * 1), μ)
        = ∑ i ∈ Finset.range ell, ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
          ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, fA A (pathSite u.1 μ (i * 1), μ) := by
      calc _ = ∑ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
            ∑ i ∈ Finset.range ell, ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1,
              fA A (pathSite u.1 μ (i * 1), μ) :=
            Finset.sum_congr rfl fun cs _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    refine le_trans (le_of_eq hswap) (Finset.sum_le_sum fun i _ => ?_)
    set H : PeriodicLatticeSite L → ℝ := fun z => fA A (pathSite z μ (i * 1), μ) with hH
    have hHn : ∀ z, 0 ≤ H z := fun z => fA_nonneg A _
    have hin : ∀ cs : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L (1 * ell)},
        ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, fA A (pathSite u.1 μ (i * 1), μ)
          ≤ ∑ z ∈ blockOf cs.1 (1 * ell), H z := by
      intro cs
      have hsub : (unitSitesOf 1 (1 * ell) cs.1).image Subtype.val ⊆ blockOf cs.1 (1 * ell) := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa [unitSitesOf] using hu
      calc ∑ u ∈ unitSitesOf 1 (1 * ell) cs.1, fA A (pathSite u.1 μ (i * 1), μ)
          = ∑ z ∈ (unitSitesOf 1 (1 * ell) cs.1).image Subtype.val, H z :=
            (Finset.sum_image (f := H) (g := Subtype.val) (s := unitSitesOf 1 (1 * ell) cs.1)
              (fun a _ b _ h => Subtype.ext h)).symm
        _ ≤ ∑ z ∈ blockOf cs.1 (1 * ell), H z :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hHn z)
    refine (Finset.sum_le_sum fun cs _ => hin cs).trans ?_
    refine (sum_blocks_le hell1 H hHn).trans (le_of_eq ?_)
    exact sum_pathSite μ (i * 1) (fun z => fA A (z, μ))
  have h3 : ∑ μ : Fin 3, ∑ i ∈ Finset.range ell, ∑ z : PeriodicLatticeSite L, fA A (z, μ)
      = (ell : ℝ) * l1 (fA A) := by
    unfold l1
    rw [Fintype.sum_prod_type_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (1 / (ell : ℝ) ^ 4) * _ ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * l1 (fA A)) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (by positivity)
    _ = (1 / (ell : ℝ) ^ 3) * l1 (fA A) := by field_simp

theorem T1_l1 {ell : ℕ} (hell : 0 < ell) (V : PeriodicLinkConfiguration SU2 L) (A : CoarseBond L 1 → SuTwo) :
    ∑ c : CoarseBond L (1 * ell), ‖unitToCoarseCov 1 ell V A c‖ ≤ (1 / (ell : ℝ) ^ 3) * l1 (fA A) :=
  (Finset.sum_le_sum fun c _ => T1_pointwise_l1 V A c).trans (T1_count hell A)

#print axioms T1_pointwise_l1
#print axioms T1_count
#print axioms T1_l1

end AdalyFormal.DLayer
