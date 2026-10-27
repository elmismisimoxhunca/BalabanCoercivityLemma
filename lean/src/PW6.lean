import PW5

/-!
# PW6 -- `massF_univ_le`: flat mass of the full height-`(j+1)` tower ≤ flat mass of the two-stratum patch
(see PW5 for the mechanism).  No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ThirdLevelArrows (pathSite_mul_coarse)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SliceCoerc (OnLat onLat_shift)

variable {L : PeriodicLatticeExtent}

theorem lcr_succ_sq' {n ell N : ℕ} (hNe : N = n * ell) (hn : 0 < n) (hell : 0 < ell) (hdvd : ∀ μ, N ∣ L μ + 1)
    (v : Bond L → SuTwo) (c : CoarseBond L N) (hcn : c.1.1 ∈ CoarseLattice L n) :
    ‖lineCoarseRestrictSuTwo N v c‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ stepBlockOf c.1.1 n ell, ∑ i ∈ Finset.range ell,
          ‖(if h : pathSite x c.2 (i * n) ∈ CoarseLattice L n then
            lineCoarseRestrictSuTwo n v (⟨pathSite x c.2 (i * n), h⟩, c.2) else 0)‖ ^ 2 := by
  subst hNe
  exact lcr_succ_sq hn hell hdvd v c hcn

theorem onLat_iff_mem {m : ℕ} (x : PeriodicLatticeSite L) : OnLat m x ↔ x ∈ CoarseLattice L m := by
  rw [mem_CoarseLattice]
  exact forall_congr' (fun μ => Nat.dvd_iff_mod_eq_zero)

section main
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1) (A : BondFnL2 L)

open Classical in
/-- the level-`j` row energy, cut off outside the patch rows. -/
noncomputable def gcut (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) (w : Bond L) : ℝ :=
  if w ∈ bondsLam (geomOf ell (j + 1) (patchTower j Rg)) j then ‖rv ell A j w‖ ^ 2 else 0

theorem gcut_nonneg (w : Bond L) : 0 ≤ gcut ell j Rg A w := by
  unfold gcut; split_ifs <;> positivity

/-- the per-row bound for a level-`(j+1)` row of the full tower that is not a patch row. -/
noncomputable def Tsum (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) (b : Bond L) : ℝ :=
  if b.1 ∈ CoarseLattice L (ell ^ (j + 1)) then
    ∑ x ∈ stepBlockOf b.1 (ell ^ j) ell, ∑ i ∈ Finset.range ell, gcut ell j Rg A (pathSite x b.2 (i * ell ^ j), b.2)
  else 0

include hell hRg hdvd in
theorem row_bound (b : Bond L)
    (hb : b ∈ bondsLam (geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L)))) (j + 1))
    (hnb : b ∉ bondsLam (geomOf ell (j + 1) (patchTower j Rg)) (j + 1)) :
    ‖rv ell A (j + 1) b‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 4) * Tsum ell j Rg A b := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hNe : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
  have hdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ)
  have hc0 : OnLat (ell ^ (j + 1)) b.1 := row_univ_coarse hdvd b hb
  have hcN : b.1 ∈ CoarseLattice L (ell ^ (j + 1)) := (onLat_iff_mem _).mp hc0
  have hcn : b.1 ∈ CoarseLattice L (ell ^ j) := by
    rw [hNe] at hcN; exact coarse_of_coarse_mul hcN
  obtain ⟨hout0, hout1⟩ := row_diff_out hell hRg hdvd b hb hnb
  rw [rv_flat hell hdvd A le_rfl b hcN]
  have hsq := lcr_succ_sq' hNe hn hell hdvd (WithLp.ofLp A) (⟨b.1, hcN⟩, b.2) hcn
  refine hsq.trans (le_of_eq ?_)
  unfold Tsum
  rw [if_pos hcN]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun i hi => ?_))
  have hpc : pathSite x b.2 (i * ell ^ j) ∈ CoarseLattice L (ell ^ j) := pathSite_mul_coarse _ hdj (by
    have := mem_stepBlockOf.mp hx
    rw [mem_CoarseLattice]; intro μ
    obtain ⟨t, ht⟩ := (this μ).2.2
    have hy := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hcn) μ)
    have : (x μ).val = (x μ).val - (b.1 μ).val + (b.1 μ).val := by have := (this μ).1; omega
    exact Nat.mod_eq_zero_of_dvd (by rw [this]; exact Nat.dvd_add (by rw [ht]; exact dvd_mul_right _ _) hy)) b.2 i
  simp only [dif_pos hpc]
  -- the stepped bond is a patch row of level j
  have hxs := mem_stepBlockOf.mp hx
  have hxb : x ∈ blockOf b.1 (ell ^ (j + 1)) := by
    rw [mem_blockOf]; intro μ
    refine ⟨(hxs μ).1, ?_⟩
    have := (hxs μ).2.1; rw [hNe]; exact this
  have hil : i < ell := Finset.mem_range.mp hi
  have hxμ : (x b.2).val + ell ^ j ≤ (b.1 b.2).val + ell ^ (j + 1) := by
    obtain ⟨t, ht⟩ := (hxs b.2).2.2
    have h1 := (hxs b.2).1
    have h2 := (hxs b.2).2.1
    have hx' : (x b.2).val = (b.1 b.2).val + ell ^ j * t := by omega
    have htl : t < ell := by
      by_contra hcon; push Not at hcon
      have : ell ^ j * ell ≤ ell ^ j * t := Nat.mul_le_mul_left _ hcon
      omega
    have h3 : ell ^ j * (t + 1) ≤ ell ^ j * ell := Nat.mul_le_mul_left _ htl
    have h4 : ell ^ j * (t + 1) = ell ^ j * t + ell ^ j := by ring
    rw [hNe]; omega
  have hiN : (i + 1) * ell ^ j ≤ ell ^ (j + 1) := by
    rw [hNe, mul_comm (ell ^ j) ell]; exact Nat.mul_le_mul_right _ hil
  have hw0 : coarseShift x (i * ell ^ j) b.2 ∉ Rg :=
    shift_out hell hRg hdvd b.1 hc0 b.2 hout0 hout1 x hxb _ (by nlinarith)
  have hw1 : coarseShift (coarseShift x (i * ell ^ j) b.2) (ell ^ j) b.2 ∉ Rg := by
    have : coarseShift (coarseShift x (i * ell ^ j) b.2) (ell ^ j) b.2 = coarseShift x ((i + 1) * ell ^ j) b.2 := by
      unfold coarseShift
      rw [← Function.iterate_add_apply]; congr 1; ring
    rw [this]
    exact shift_out hell hRg hdvd b.1 hc0 b.2 hout0 hout1 x hxb _ (by nlinarith)
  have hrow : ((pathSite x b.2 (i * ell ^ j), b.2) : Bond L) ∈ bondsLam (geomOf ell (j + 1) (patchTower j Rg)) j :=
    row_j_of_out hell hRg _ ((onLat_iff_mem _).mpr hpc) b.2 hw0 hw1
  unfold gcut
  rw [if_pos hrow, rv_flat hell hdvd A (Nat.le_succ j) _ hpc]


include hell hdvd in
theorem tsum_count : ∑ b : Bond L, Tsum ell j Rg A b ≤ (ell : ℝ) * ∑ w : Bond L, gcut ell j Rg A w := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hNe : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
  have hdN : ∀ μ, ell ^ j * ell ∣ L μ + 1 := fun μ => by rw [← hNe]; exact hdvd μ
  have hdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ)
  -- sum over bonds = sum over directions of sums over sites
  have hsplit : ∀ F : Bond L → ℝ, ∑ b : Bond L, F b = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, F (y, μ) := by
    intro F
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit, hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have hT : ∑ y : PeriodicLatticeSite L, Tsum ell j Rg A (y, μ)
      = ∑ y ∈ CoarseLattice L (ell ^ j * ell), ∑ x ∈ stepBlockOf y (ell ^ j) ell,
          ∑ i ∈ Finset.range ell, gcut ell j Rg A (pathSite x μ (i * ell ^ j), μ) := by
    unfold Tsum
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun y _ => rfl)
    ext y; simp [hNe]
  rw [hT, sum_partition hn hell hdN (fun x => ∑ i ∈ Finset.range ell, gcut ell j Rg A (pathSite x μ (i * ell ^ j), μ)),
    Finset.sum_comm]
  have hle : ∀ i ∈ Finset.range ell, ∑ x ∈ CoarseLattice L (ell ^ j), gcut ell j Rg A (pathSite x μ (i * ell ^ j), μ)
      ≤ ∑ x ∈ CoarseLattice L (ell ^ j), gcut ell j Rg A (x, μ) :=
    fun i _ => sum_shift_le hdj μ i (fun x => gcut ell j Rg A (x, μ)) (fun x => gcut_nonneg A _)
  calc ∑ i ∈ Finset.range ell, ∑ x ∈ CoarseLattice L (ell ^ j), gcut ell j Rg A (pathSite x μ (i * ell ^ j), μ)
      ≤ ∑ i ∈ Finset.range ell, ∑ x ∈ CoarseLattice L (ell ^ j), gcut ell j Rg A (x, μ) := Finset.sum_le_sum hle
    _ = (ell : ℝ) * ∑ x ∈ CoarseLattice L (ell ^ j), gcut ell j Rg A (x, μ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (ell : ℝ) * ∑ y : PeriodicLatticeSite L, gcut ell j Rg A (y, μ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => gcut_nonneg A _)

include hell hRg hdvd in
/-- **flat mass comparison**. -/
theorem massF_univ_le (a : ℝ) (ha : 0 ≤ a) :
    massF (geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L)))) a A
      ≤ massF (geomOf ell (j + 1) (patchTower j Rg)) a A := by
  classical
  set GU := geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L))) with hGU
  set GR := geomOf ell (j + 1) (patchTower j Rg) with hGR
  set w : ℕ → Bond L → ℝ := fun i b => a * (ell : ℝ) ^ i * ‖rv ell A i b‖ ^ 2 with hw
  have hw0 : ∀ i b, 0 ≤ w i b := fun i b => by simp only [hw]; positivity
  rw [massF_eq, massF_eq]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (n := j + 1)]
  -- the lower levels of the full tower are empty
  have hlowU : ∑ i : Fin (j + 1), ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GU (Fin.castSucc i : ℕ)),
      a * (ell : ℝ) ^ ((Fin.castSucc i : Fin (j + 2)) : ℕ) * ‖rv ell A (Fin.castSucc i : ℕ) b‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun b hb => ?_))
    exact absurd (Finset.mem_filter.mp hb).2 (not_row_lt_univ (Nat.lt_succ_iff.mp i.isLt) b)
  rw [hlowU, zero_add]
  -- keep only level j of the patch's lower sum
  have hlowR : ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), w j b
      ≤ ∑ i : Fin (j + 1), ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR (Fin.castSucc i : ℕ)),
        a * (ell : ℝ) ^ ((Fin.castSucc i : Fin (j + 2)) : ℕ) * ‖rv ell A (Fin.castSucc i : ℕ) b‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun i : Fin (j + 1) => ∑ b ∈ Finset.univ.filter
        (fun b => b ∈ bondsLam GR (Fin.castSucc i : ℕ)),
        a * (ell : ℝ) ^ ((Fin.castSucc i : Fin (j + 2)) : ℕ) * ‖rv ell A (Fin.castSucc i : ℕ) b‖ ^ 2)
      (fun i _ => Finset.sum_nonneg (fun b _ => hw0 _ _)) (Finset.mem_univ (Fin.last j))
    simpa using this
  simp only [Fin.val_last] at *
  -- split the top level of the full tower
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun b => b ∈ bondsLam GU (j + 1)))
    (fun b => b ∈ bondsLam GR (j + 1))]
  have htop : ∑ b ∈ (Finset.univ.filter (fun b => b ∈ bondsLam GU (j + 1))).filter (fun b => b ∈ bondsLam GR (j + 1)),
      w (j + 1) b ≤ ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR (j + 1)), w (j + 1) b := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hw0 _ _)
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.2
  -- the rows of the full tower that are not patch rows
  have hdiff : ∑ b ∈ (Finset.univ.filter (fun b => b ∈ bondsLam GU (j + 1))).filter (fun b => ¬ b ∈ bondsLam GR (j + 1)),
      w (j + 1) b ≤ ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), w j b := by
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have hellR0 : (0 : ℝ) < ell := by exact_mod_cast hell
    have h1 : ∀ b ∈ (Finset.univ.filter (fun b => b ∈ bondsLam GU (j + 1))).filter (fun b => ¬ b ∈ bondsLam GR (j + 1)),
        w (j + 1) b ≤ a * (ell : ℝ) ^ (j + 1) * ((1 / (ell : ℝ) ^ 4) * Tsum ell j Rg A b) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [hw]
      exact mul_le_mul_of_nonneg_left (row_bound hell hRg hdvd A b hb.1 hb.2) (by positivity)
    have hT0 : ∀ b, 0 ≤ Tsum ell j Rg A b := by
      intro b; unfold Tsum; split_ifs
      · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => gcut_nonneg A _))
      · exact le_rfl
    have hgc : ∑ w' : Bond L, gcut ell j Rg A w' = ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), ‖rv ell A j b‖ ^ 2 := by
      unfold gcut; rw [Finset.sum_filter]
    calc _ ≤ ∑ b ∈ (Finset.univ.filter (fun b => b ∈ bondsLam GU (j + 1))).filter (fun b => ¬ b ∈ bondsLam GR (j + 1)),
          a * (ell : ℝ) ^ (j + 1) * ((1 / (ell : ℝ) ^ 4) * Tsum ell j Rg A b) := Finset.sum_le_sum h1
      _ ≤ ∑ b : Bond L, a * (ell : ℝ) ^ (j + 1) * ((1 / (ell : ℝ) ^ 4) * Tsum ell j Rg A b) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => by
            have := hT0 b; positivity)
      _ = a * (ell : ℝ) ^ (j + 1) * (1 / (ell : ℝ) ^ 4) * ∑ b : Bond L, Tsum ell j Rg A b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => by ring)
      _ ≤ a * (ell : ℝ) ^ (j + 1) * (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ w' : Bond L, gcut ell j Rg A w') :=
          mul_le_mul_of_nonneg_left (tsum_count hell hdvd A) (by positivity)
      _ = (1 / (ell : ℝ) ^ 2) * ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), w j b := by
          rw [hgc]
          have hS : ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), w j b
              = a * (ell : ℝ) ^ j * ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), ‖rv ell A j b‖ ^ 2 := by
            simp only [hw]; rw [Finset.mul_sum]
          rw [hS, pow_succ]
          field_simp
      _ ≤ ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j), w j b := by
          have hS := Finset.sum_nonneg (fun b (_ : b ∈ Finset.univ.filter (fun b => b ∈ bondsLam GR j)) => hw0 j b)
          have : 1 / (ell : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          nlinarith
  have hfin := add_le_add htop hdiff
  simp only [hw] at hfin hlowR
  linarith

end main

#print axioms row_bound
#print axioms tsum_count
#print axioms massF_univ_le

end AdalyFormal.M1Patch
