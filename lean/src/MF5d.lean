import MF5c

/-!
# MF5d -- the norm of the flat bond right inverse: `Σ_b ‖bondE n W b‖² ≤ 16 n³ Σ_c ‖W c‖²` (Schur test, FlatExt FE2 `schur`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M0Finish

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-- the majorant of the kernel -/
noncomputable def bM (n : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (c : CoarseBond L n) : ℝ :=
  if c.2 = μ then 4 * ∏ ν : Fin 3, (if (x ν - c.1.1 ν).val < n then (1 : ℝ) else 0) else 0

theorem abs_fac_le (n : ℕ) (μ ν : Fin 3) (t : ℕ) :
    |fac n μ ν t| ≤ (if ν = μ then 4 else 1) * (if t < n then (1 : ℝ) else 0) := by
  unfold fac
  by_cases hν : ν = μ
  · rw [if_pos hν, if_pos hν]
    by_cases ht : t < n
    · rw [if_pos ht, mul_one]; exact abs_gprof_le n t
    · rw [if_neg ht, mul_zero, gprof_eq_zero n t (by omega), abs_zero]
  · rw [if_neg hν, if_neg hν, one_mul]
    split_ifs <;> simp

theorem abs_bK_le (n : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (c : CoarseBond L n) :
    |bK n x μ c| ≤ bM n x μ c := by
  unfold bK bM
  by_cases hc : c.2 = μ
  · rw [if_pos hc, if_pos hc, Finset.abs_prod]
    have h : ∀ ν ∈ (univ : Finset (Fin 3)), |fac n μ ν ((x ν - c.1.1 ν).val)|
        ≤ (if ν = μ then 4 else 1) * (if (x ν - c.1.1 ν).val < n then (1 : ℝ) else 0) :=
      fun ν _ => abs_fac_le n μ ν _
    refine (Finset.prod_le_prod (fun ν _ => abs_nonneg _) h).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_mul_prod_compl μ, if_pos rfl]
    have : ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), (if ν = μ then (4 : ℝ) else 1) = 1 := by
      refine Finset.prod_eq_one (fun ν hν => ?_)
      have hne : ν ≠ μ := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      rw [if_neg hne]
    rw [this, mul_one]
  · rw [if_neg hc, if_neg hc, abs_zero]

theorem coarse_pi (n : ℕ) :
    CoarseLattice L n = Fintype.piFinset (fun ν => univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0)) := by
  ext y
  simp [mem_CoarseLattice, Fintype.mem_piFinset]

theorem row_coord_le {N : ℕ} [NeZero N] (n : ℕ) (hn : 0 < n) (hnN : n ∣ N) (x : Fin N) :
    ∑ t ∈ univ.filter (fun t : Fin N => t.val % n = 0), (if (x - t).val < n then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_filter]
  have h := AdalyFormal.FlatExt.row_ind_le_one n hnN x 0
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) h
  by_cases h1 : t.val % n = 0
  · have hd : n ∣ t.val := Nat.dvd_of_mod_eq_zero h1
    by_cases h2 : (x - t).val < n
    · rw [if_pos h1, if_pos h2, if_pos ⟨hd, Nat.div_eq_of_lt h2⟩]
    · rw [if_pos h1, if_neg h2, if_neg]
      rintro ⟨-, h3⟩
      exact h2 (by rw [Nat.div_eq_zero_iff] at h3; omega)
  · rw [if_neg h1, if_neg]
    rintro ⟨h3, -⟩
    exact h1 (Nat.mod_eq_zero_of_dvd h3)

theorem col_coord_le {N : ℕ} [NeZero N] (n : ℕ) (hn : 0 < n) (y : Fin N) :
    ∑ a : Fin N, (if (a - y).val < n then (1 : ℝ) else 0) ≤ n := by
  have h := AdalyFormal.FlatExt.col_ind_le n hn y 0
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun a _ => ?_))) h
  by_cases h2 : (a - y).val < n
  · rw [if_pos h2, if_pos (Nat.div_eq_of_lt h2)]
  · rw [if_neg h2, if_neg]
    intro h3; rw [Nat.div_eq_zero_iff] at h3; omega

theorem bM_row (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (b : Bond L) :
    ∑ c : CoarseBond L n, bM n b.1 b.2 c ≤ 4 := by
  classical
  have hsplit : ∑ c : CoarseBond L n, bM n b.1 b.2 c
      = ∑ y : {y // y ∈ CoarseLattice L n}, 4 * ∏ ν : Fin 3, (if (b.1 ν - y.1 ν).val < n then (1 : ℝ) else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_eq_single b.2]
    · simp [bM]
    · intro μ' _ hμ'; simp [bM, hμ']
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsplit, ← Finset.mul_sum]
  have hsub : ∑ y : {y // y ∈ CoarseLattice L n}, ∏ ν : Fin 3, (if (b.1 ν - y.1 ν).val < n then (1 : ℝ) else 0)
      = ∑ y ∈ CoarseLattice L n, ∏ ν : Fin 3, (if (b.1 ν - y ν).val < n then (1 : ℝ) else 0) := by
    convert Finset.sum_coe_sort (CoarseLattice L n)
      (fun y => ∏ ν : Fin 3, (if (b.1 ν - y ν).val < n then (1 : ℝ) else 0)) using 2
    exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)
  rw [hsub, coarse_pi, ← Finset.prod_univ_sum (t := fun ν => univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0))
    (f := fun ν t => if (b.1 ν - t).val < n then (1 : ℝ) else 0)]
  have hf : ∏ ν : Fin 3, ∑ t ∈ univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0),
      (if (b.1 ν - t).val < n then (1 : ℝ) else 0) ≤ 1 :=
    Finset.prod_le_one (fun ν _ => Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num))
      (fun ν _ => row_coord_le n hn (hdvd ν) (b.1 ν))
  linarith

theorem bM_col (n : ℕ) (hn : 0 < n) (c : CoarseBond L n) :
    ∑ b : Bond L, bM n b.1 b.2 c ≤ 4 * (n : ℝ) ^ 3 := by
  classical
  have hsplit : ∑ b : Bond L, bM n b.1 b.2 c
      = ∑ x : PeriodicLatticeSite L, 4 * ∏ ν : Fin 3, (if (x ν - c.1.1 ν).val < n then (1 : ℝ) else 0) := by
    rw [show (∑ b : Bond L, bM n b.1 b.2 c) = ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, bM n x μ c from
      Fintype.sum_prod_type _]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single c.2]
    · simp [bM]
    · intro μ' _ hμ'; simp [bM, Ne.symm hμ']
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsplit, ← Finset.mul_sum]
  have hpi : ∑ x : PeriodicLatticeSite L, ∏ ν : Fin 3, (if (x ν - c.1.1 ν).val < n then (1 : ℝ) else 0)
      = ∏ ν : Fin 3, ∑ a : Fin (L ν + 1), (if (a - c.1.1 ν).val < n then (1 : ℝ) else 0) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hpi]
  have hf : ∏ ν : Fin 3, ∑ a : Fin (L ν + 1), (if (a - c.1.1 ν).val < n then (1 : ℝ) else 0) ≤ ∏ _ν : Fin 3, (n : ℝ) :=
    Finset.prod_le_prod (fun ν _ => Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num))
      (fun ν _ => col_coord_le n hn (c.1.1 ν))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hf
  linarith

/-- **`‖E W‖² ≤ 16 n³ ‖W‖²`** -/
theorem bondE_norm_sq (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖bondE n W b‖ ^ 2 ≤ 16 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  have h := AdalyFormal.FlatExt.schur (fun (b : Bond L) (c : CoarseBond L n) => bK n b.1 b.2 c)
    (fun b c => bM n b.1 b.2 c) (fun b c => abs_bK_le n b.1 b.2 c) 4 (4 * (n : ℝ) ^ 3) (by norm_num)
    (fun b => bM_row n hn hdvd b) (fun c => bM_col n hn c) W
  calc ∑ b : Bond L, ‖bondE n W b‖ ^ 2 = ∑ b : Bond L, ‖∑ c : CoarseBond L n, bK n b.1 b.2 c • W c‖ ^ 2 := rfl
    _ ≤ 4 * (4 * (n : ℝ) ^ 3) * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := h
    _ = 16 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by ring

#print axioms abs_fac_le
#print axioms abs_bK_le
#print axioms coarse_pi
#print axioms row_coord_le
#print axioms col_coord_le
#print axioms bM_row
#print axioms bM_col
#print axioms bondE_norm_sq

end AdalyFormal.M0Finish
