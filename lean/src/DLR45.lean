import DLR44
import MF5d

/-!
# DL45 -- the size and the GRADIENT of the smooth flat bond right inverse (Schur tests on product kernels)

* `prod_schur` : a site × coarse-bond kernel majorised by `[c.2 = μ] Π_ν m_ν((y_ν − c_ν) mod)` has
  `Σ_y ‖Σ_c K(y,c) W c‖² ≤ (Π_ν R_ν)(Π_ν C_ν) Σ_{c.2 = μ} ‖W c‖²` (1D row sums `R_ν` over coarse coordinates, column sums `C_ν`).
* **`gbondE_norm_sq`** : `Σ_b ‖gbondE g h n W b‖² ≤ (F_g F_h²)² n³ ‖W‖²` for `SProf` profiles.
* **`gbondE_grad_sq`** : for every shift direction `ν₀`:
  `Σ_b ‖x(b.1 + e_{ν₀}, b.2) − x(b)‖² ≤ 16 n · max(D_g² F_h⁴, D_h² F_g² F_h²) ‖W‖²` — a gradient of order `1/n` per fine step,
  i.e. the field is smooth at the block scale (this is what makes the extension energy `O(n)` instead of `O(n²)`).
* `sbondE_norm_sq` (`≤ 410.0625 n³‖W‖²`), `sbondE_grad_sq` (`≤ 419904 n ‖W‖²`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.M0Finish (coarse_pi row_coord_le col_coord_le)

variable {L : PeriodicLatticeExtent}

/-! ## 1D counting -/

theorem row_eqlast_le {N : ℕ} [NeZero N] (n : ℕ) (a : Fin N) :
    ∑ t ∈ univ.filter (fun t : Fin N => t.val % n = 0), (if (a - t).val = N - 1 then (1 : ℝ) else 0) ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by split_ifs <;> norm_num)) ?_
  rw [Finset.sum_boole]
  have : (univ.filter (fun t : Fin N => (a - t).val = N - 1)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun t1 h1 t2 h2 => ?_)
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have e : a - t1 = a - t2 := Fin.ext (by rw [h1, h2])
    exact sub_right_injective e
  exact_mod_cast this

theorem col_or_le {N : ℕ} [NeZero N] (n : ℕ) (t : Fin N) :
    ∑ a : Fin N, (if (a - t).val < n ∨ (a - t).val = N - 1 then (1 : ℝ) else 0) ≤ n + 1 := by
  have hs : ∑ a : Fin N, (if (a - t).val < n ∨ (a - t).val = N - 1 then (1 : ℝ) else 0)
      = ∑ d : Fin N, (if d.val < n ∨ d.val = N - 1 then (1 : ℝ) else 0) :=
    Fintype.sum_equiv (Equiv.subRight t) _ _ (fun a => rfl)
  rw [hs]
  have h1 : ∀ d : Fin N, (if d.val < n ∨ d.val = N - 1 then (1 : ℝ) else 0)
      ≤ (if d.val < n then (1 : ℝ) else 0) + (if d.val = N - 1 then (1 : ℝ) else 0) := by
    intro d; split_ifs <;> simp_all
  refine (Finset.sum_le_sum (fun d _ => h1 d)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have c1 : (univ.filter (fun d : Fin N => d.val < n)).card ≤ n := by
    have : (univ.filter (fun d : Fin N => d.val < n)).card ≤ (Finset.range n).card := by
      refine Finset.card_le_card_of_injOn (fun d => d.val) (fun d hd => ?_) (fun a _ b _ hab => Fin.ext hab)
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hd
      simpa using hd
    simpa using this
  have c2 : (univ.filter (fun d : Fin N => d.val = N - 1)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (by rw [ha, hb])
  have : ((univ.filter (fun d : Fin N => d.val < n)).card : ℝ) + ((univ.filter (fun d : Fin N => d.val = N - 1)).card : ℝ)
      ≤ (n : ℝ) + 1 := by
    have h1' : ((univ.filter (fun d : Fin N => d.val < n)).card : ℝ) ≤ n := by exact_mod_cast c1
    have h2' : ((univ.filter (fun d : Fin N => d.val = N - 1)).card : ℝ) ≤ 1 := by exact_mod_cast c2
    linarith
  exact this

theorem row_or_le {N : ℕ} [NeZero N] (n : ℕ) (hn : 0 < n) (hnN : n ∣ N) (a : Fin N) :
    ∑ t ∈ univ.filter (fun t : Fin N => t.val % n = 0),
      (if (a - t).val < n ∨ (a - t).val = N - 1 then (1 : ℝ) else 0) ≤ 2 := by
  have h1 : ∀ t : Fin N, (if (a - t).val < n ∨ (a - t).val = N - 1 then (1 : ℝ) else 0)
      ≤ (if (a - t).val < n then (1 : ℝ) else 0) + (if (a - t).val = N - 1 then (1 : ℝ) else 0) := by
    intro t; split_ifs <;> simp_all
  refine (Finset.sum_le_sum (fun t _ => h1 t)).trans ?_
  rw [Finset.sum_add_distrib]
  have := row_coord_le n hn hnN a
  have := row_eqlast_le n a
  linarith

/-! ## the product-kernel Schur test -/

/-- **Schur test for product kernels** (fixed bond direction `μ`, restricted output `Σ_{c.2 = μ}`) -/
theorem prod_schur (n : ℕ) (μ : Fin 3) (m : Fin 3 → ℕ → ℝ) (hm0 : ∀ ν t, 0 ≤ m ν t) (R C : Fin 3 → ℝ)
    (hR : ∀ ν (a : Fin (L ν + 1)), ∑ t ∈ univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0), m ν ((a - t).val) ≤ R ν)
    (hC : ∀ ν (t : Fin (L ν + 1)), ∑ a : Fin (L ν + 1), m ν ((a - t).val) ≤ C ν)
    (K : PeriodicLatticeSite L → CoarseBond L n → ℝ)
    (hK : ∀ y c, |K y c| ≤ if c.2 = μ then ∏ ν : Fin 3, m ν ((y ν - c.1.1 ν).val) else 0)
    (W : CoarseBond L n → SuTwo) :
    ∑ y : PeriodicLatticeSite L, ‖∑ c : CoarseBond L n, K y c • W c‖ ^ 2
      ≤ (∏ ν : Fin 3, R ν) * (∏ ν : Fin 3, C ν) * ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 := by
  classical
  set M : PeriodicLatticeSite L → CoarseBond L n → ℝ :=
    fun y c => if c.2 = μ then ∏ ν : Fin 3, m ν ((y ν - c.1.1 ν).val) else 0 with hMdef
  have hR0 : ∀ ν, 0 ≤ R ν := fun ν =>
    le_trans (Finset.sum_nonneg (fun t _ => hm0 ν _)) (hR ν 0)
  have hrow : ∀ y, ∑ c : CoarseBond L n, M y c ≤ ∏ ν : Fin 3, R ν := by
    intro y
    have hsplit : ∑ c : CoarseBond L n, M y c
        = ∑ z : {z // z ∈ CoarseLattice L n}, ∏ ν : Fin 3, m ν ((y ν - z.1 ν).val) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.sum_eq_single μ]
      · simp [hMdef]
      · intro μ' _ hμ'; simp [hMdef, hμ']
      · intro hh; exact absurd (Finset.mem_univ _) hh
    rw [hsplit]
    have hsub : ∑ z : {z // z ∈ CoarseLattice L n}, ∏ ν : Fin 3, m ν ((y ν - z.1 ν).val)
        = ∑ z ∈ CoarseLattice L n, ∏ ν : Fin 3, m ν ((y ν - z ν).val) := by
      convert Finset.sum_coe_sort (CoarseLattice L n) (fun z => ∏ ν : Fin 3, m ν ((y ν - z ν).val)) using 2
      exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)
    rw [hsub, coarse_pi, ← Finset.prod_univ_sum (t := fun ν => univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0))
      (f := fun ν t => m ν ((y ν - t).val))]
    exact Finset.prod_le_prod (fun ν _ => Finset.sum_nonneg (fun t _ => hm0 ν _)) (fun ν _ => hR ν (y ν))
  have hcol : ∀ c, ∑ y : PeriodicLatticeSite L, M y c ≤ ∏ ν : Fin 3, C ν := by
    intro c
    by_cases hc : c.2 = μ
    · have h1 : ∑ y : PeriodicLatticeSite L, M y c = ∏ ν : Fin 3, ∑ a : Fin (L ν + 1), m ν ((a - c.1.1 ν).val) := by
        simp only [hMdef, if_pos hc]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [h1]
      exact Finset.prod_le_prod (fun ν _ => Finset.sum_nonneg (fun t _ => hm0 ν _)) (fun ν _ => hC ν (c.1.1 ν))
    · have h1 : ∑ y : PeriodicLatticeSite L, M y c = 0 := by simp [hMdef, hc]
      rw [h1]
      exact Finset.prod_nonneg (fun ν _ => le_trans (Finset.sum_nonneg (fun t _ => hm0 ν _)) (hC ν 0))
  have hKM : ∀ y c, |K y c| ≤ M y c := hK
  have hKw : ∀ y, ∑ c : CoarseBond L n, K y c • W c = ∑ c : CoarseBond L n, K y c • (if c.2 = μ then W c else 0) := by
    intro y
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : c.2 = μ
    · rw [if_pos hc]
    · have h0 : K y c = 0 := by
        have := hK y c; rw [if_neg hc] at this; exact abs_nonpos_iff.mp this
      rw [h0, zero_smul, zero_smul]
  simp only [hKw]
  exact AdalyFormal.FlatExt.schur K M hKM (∏ ν : Fin 3, R ν) (∏ ν : Fin 3, C ν)
    (Finset.prod_nonneg (fun ν _ => hR0 ν)) hrow hcol (fun c => if c.2 = μ then W c else 0)

/-- the direction pieces add up to `‖W‖²` -/
theorem sum_dir_split (n : ℕ) (W : CoarseBond L n → SuTwo) :
    ∑ μ : Fin 3, ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 = ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single c.2]
  · rw [if_pos rfl]
  · intro μ _ hμ; rw [if_neg (Ne.symm hμ), norm_zero]; ring
  · intro hh; exact absurd (Finset.mem_univ _) hh

/-! ## the norm -/

theorem abs_gfac_le {n : ℕ} {g h : ℕ → ℝ} {Fg Dg Fh Dh : ℝ} (hg : SProf n g Fg Dg) (hh : SProf n h Fh Dh)
    (μ ν : Fin 3) (t : ℕ) : |gfac g h μ ν t| ≤ (if ν = μ then Fg else Fh) * (if t < n then (1 : ℝ) else 0) := by
  unfold gfac
  by_cases hν : ν = μ
  · rw [if_pos hν, if_pos hν]
    by_cases ht : t < n
    · rw [if_pos ht, mul_one]; exact hg.bnd t
    · rw [if_neg ht, mul_zero, hg.zero t (by omega), abs_zero]
  · rw [if_neg hν, if_neg hν]
    by_cases ht : t < n
    · rw [if_pos ht, mul_one]; exact hh.bnd t
    · rw [if_neg ht, mul_zero, hh.zero t (by omega), abs_zero]

theorem gbondE_norm_sq {n : ℕ} {g h : ℕ → ℝ} {Fg Dg Fh Dh : ℝ} (hg : SProf n g Fg Dg) (hh : SProf n h Fh Dh)
    (hdvd : ∀ ν, n ∣ L ν + 1) (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖gbondE g h n W b‖ ^ 2 ≤ (Fg * Fh ^ 2) ^ 2 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  classical
  have hn := hg.pos
  have hFg := hg.F_nonneg
  have hFh := hh.F_nonneg
  have hμ : ∀ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖gbondE g h n W (y, μ)‖ ^ 2
      ≤ (Fg * Fh ^ 2) ^ 2 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 := by
    intro μ
    set m : Fin 3 → ℕ → ℝ := fun ν t => (if ν = μ then Fg else Fh) * (if t < n then (1 : ℝ) else 0) with hm
    have hm0 : ∀ ν t, 0 ≤ m ν t := fun ν t => by simp only [hm]; split_ifs <;> positivity
    have hS := prod_schur n μ m hm0 (fun ν => if ν = μ then Fg else Fh) (fun ν => (if ν = μ then Fg else Fh) * n)
      (fun ν a => by
        simp only [hm, ← Finset.mul_sum]
        have := row_coord_le n hn (hdvd ν) a
        calc (if ν = μ then Fg else Fh) * ∑ t ∈ univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0),
              (if (a - t).val < n then (1 : ℝ) else 0) ≤ (if ν = μ then Fg else Fh) * 1 :=
              mul_le_mul_of_nonneg_left this (by split_ifs <;> assumption)
          _ = _ := mul_one _)
      (fun ν t => by
        simp only [hm, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (col_coord_le n hn t) (by split_ifs <;> assumption))
      (fun y c => gbK g h n y μ c)
      (fun y c => by
        unfold gbK
        by_cases hc : c.2 = μ
        · rw [if_pos hc, if_pos hc, Finset.abs_prod]
          exact Finset.prod_le_prod (fun ν _ => abs_nonneg _) (fun ν _ => abs_gfac_le hg hh μ ν _)
        · rw [if_neg hc, if_neg hc, abs_zero])
      W
    have e1 : (∏ ν : Fin 3, (if ν = μ then Fg else Fh)) * (∏ ν : Fin 3, (if ν = μ then Fg else Fh) * (n : ℝ))
        = (Fg * Fh ^ 2) ^ 2 * (n : ℝ) ^ 3 := by
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      fin_cases μ <;> simp <;> ring
    rw [e1] at hS
    exact hS
  calc ∑ b : Bond L, ‖gbondE g h n W b‖ ^ 2
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖gbondE g h n W (y, μ)‖ ^ 2 := by
        rw [Fintype.sum_prod_type_right]
    _ ≤ ∑ μ : Fin 3, (Fg * Fh ^ 2) ^ 2 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 :=
        Finset.sum_le_sum (fun μ _ => hμ μ)
    _ = (Fg * Fh ^ 2) ^ 2 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
        rw [← Finset.mul_sum, sum_dir_split]

/-! ## the gradient -/

theorem shift_val_sub {N : ℕ} [NeZero N] (a c : Fin N) : ((a + 1) - c).val = ((a - c).val + 1) % N := by
  have e : (a + 1) - c = (a - c) + 1 := by abel
  rw [e, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

theorem shift_apply (y : PeriodicLatticeSite L) (ν0 ν : Fin 3) :
    (periodicLatticeShift y ν0) ν = if ν = ν0 then y ν + 1 else y ν := by
  unfold periodicLatticeShift
  by_cases h : ν = ν0
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

/-- the 1D majorant of the shift difference in direction `ν₀` -/
noncomputable def gmaj (n : ℕ) (μ ν0 : Fin 3) (Fg Dg Fh Dh : ℝ) (N : Fin 3 → ℕ) (ν : Fin 3) (t : ℕ) : ℝ :=
  if ν = ν0 then (2 * (if ν = μ then Dg else Dh) / n) * (if t < n ∨ t = N ν - 1 then (1 : ℝ) else 0)
  else (if ν = μ then Fg else Fh) * (if t < n then (1 : ℝ) else 0)

theorem gbK_shift_le {n : ℕ} {g h : ℕ → ℝ} {Fg Dg Fh Dh : ℝ} (hg : SProf n g Fg Dg) (hh : SProf n h Fh Dh)
    (hdvd : ∀ ν, n ∣ L ν + 1) (μ ν0 : Fin 3) (y : PeriodicLatticeSite L) (c : CoarseBond L n) :
    |gbK g h n (periodicLatticeShift y ν0) μ c - gbK g h n y μ c|
      ≤ if c.2 = μ then ∏ ν : Fin 3, gmaj n μ ν0 Fg Dg Fh Dh (fun ν => L ν + 1) ν ((y ν - c.1.1 ν).val) else 0 := by
  classical
  unfold gbK
  by_cases hc : c.2 = μ
  · rw [if_pos hc, if_pos hc, if_pos hc]
    rw [Fintype.prod_eq_mul_prod_compl ν0, Fintype.prod_eq_mul_prod_compl ν0, Fintype.prod_eq_mul_prod_compl ν0]
    have hrest : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), gfac g h μ ν (((periodicLatticeShift y ν0) ν - c.1.1 ν).val)
        = ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), gfac g h μ ν ((y ν - c.1.1 ν).val) := by
      refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ ν0 := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      rw [shift_apply, if_neg hne]
    have h0 : ((periodicLatticeShift y ν0) ν0 - c.1.1 ν0).val = ((y ν0 - c.1.1 ν0).val + 1) % (L ν0 + 1) := by
      rw [shift_apply, if_pos rfl, shift_val_sub]
    rw [hrest, h0, ← sub_mul, abs_mul]
    have hn : (0 : ℝ) < n := by exact_mod_cast hg.pos
    have hnN : n ≤ L ν0 + 1 := Nat.le_of_dvd (by omega) (hdvd ν0)
    -- the step factor
    have hstep : |gfac g h μ ν0 (((y ν0 - c.1.1 ν0).val + 1) % (L ν0 + 1)) - gfac g h μ ν0 ((y ν0 - c.1.1 ν0).val)|
        ≤ gmaj n μ ν0 Fg Dg Fh Dh (fun ν => L ν + 1) ν0 ((y ν0 - c.1.1 ν0).val) := by
      unfold gmaj gfac
      rw [if_pos rfl]
      by_cases hνμ : ν0 = μ
      · rw [if_pos hνμ, if_pos hνμ, if_pos hνμ]
        have := cyc_step_le hg (L ν0 + 1) ((y ν0 - c.1.1 ν0).val) hnN (y ν0 - c.1.1 ν0).isLt
        refine this.trans (le_of_eq ?_)
        split_ifs <;> simp_all
      · rw [if_neg hνμ, if_neg hνμ, if_neg hνμ]
        have := cyc_step_le hh (L ν0 + 1) ((y ν0 - c.1.1 ν0).val) hnN (y ν0 - c.1.1 ν0).isLt
        refine this.trans (le_of_eq ?_)
        split_ifs <;> simp_all
    have hothers : |∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), gfac g h μ ν ((y ν - c.1.1 ν).val)|
        ≤ ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), gmaj n μ ν0 Fg Dg Fh Dh (fun ν => L ν + 1) ν ((y ν - c.1.1 ν).val) := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod (fun ν _ => abs_nonneg _) (fun ν hν => ?_)
      have hne : ν ≠ ν0 := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      unfold gmaj
      rw [if_neg hne]
      exact abs_gfac_le hg hh μ ν _
    have hg0 : 0 ≤ gmaj n μ ν0 Fg Dg Fh Dh (fun ν => L ν + 1) ν0 ((y ν0 - c.1.1 ν0).val) :=
      le_trans (abs_nonneg _) hstep
    exact mul_le_mul hstep hothers (abs_nonneg _) hg0
  · rw [if_neg hc, if_neg hc, if_neg hc, sub_zero, abs_zero]

theorem gbondE_grad_sq {n : ℕ} {g h : ℕ → ℝ} {Fg Dg Fh Dh : ℝ} (hg : SProf n g Fg Dg) (hh : SProf n h Fh Dh)
    (hdvd : ∀ ν, n ∣ L ν + 1) (ν0 : Fin 3) (G : ℝ)
    (hG : ∀ μ : Fin 3, 8 * (if ν0 = μ then Dg else Dh) ^ 2 * (n + 1)
        * ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh) ^ 2 ≤ G * n)
    (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖gbondE g h n W (periodicLatticeShift b.1 ν0, b.2) - gbondE g h n W b‖ ^ 2
      ≤ G * n * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  classical
  have hn := hg.pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hFg := hg.F_nonneg
  have hFh := hh.F_nonneg
  have hDg := hg.D_nonneg
  have hDh := hh.D_nonneg
  have hμ : ∀ μ : Fin 3, ∑ y : PeriodicLatticeSite L,
      ‖gbondE g h n W (periodicLatticeShift y ν0, μ) - gbondE g h n W (y, μ)‖ ^ 2
      ≤ G * n * ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 := by
    intro μ
    set m := gmaj n μ ν0 Fg Dg Fh Dh (fun ν => L ν + 1) with hm
    have hm0 : ∀ ν t, 0 ≤ m ν t := fun ν t => by
      simp only [hm, gmaj]; split_ifs <;> positivity
    set R : Fin 3 → ℝ := fun ν => if ν = ν0 then (2 * (if ν = μ then Dg else Dh) / n) * 2 else (if ν = μ then Fg else Fh)
      with hR
    set C : Fin 3 → ℝ := fun ν => if ν = ν0 then (2 * (if ν = μ then Dg else Dh) / n) * (n + 1)
      else (if ν = μ then Fg else Fh) * n with hC
    have hrow : ∀ ν (a : Fin (L ν + 1)), ∑ t ∈ univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0), m ν ((a - t).val)
        ≤ R ν := by
      intro ν a
      simp only [hm, hR, gmaj]
      by_cases hν : ν = ν0
      · simp only [if_pos hν]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (row_or_le n hn (hdvd ν) a) (by split_ifs <;> positivity)
      · simp only [if_neg hν]
        rw [← Finset.mul_sum]
        calc (if ν = μ then Fg else Fh) * ∑ t ∈ univ.filter (fun t : Fin (L ν + 1) => t.val % n = 0),
              (if (a - t).val < n then (1 : ℝ) else 0) ≤ (if ν = μ then Fg else Fh) * 1 :=
              mul_le_mul_of_nonneg_left (row_coord_le n hn (hdvd ν) a) (by split_ifs <;> assumption)
          _ = _ := mul_one _
    have hcol : ∀ ν (t : Fin (L ν + 1)), ∑ a : Fin (L ν + 1), m ν ((a - t).val) ≤ C ν := by
      intro ν t
      simp only [hm, hC, gmaj]
      by_cases hν : ν = ν0
      · simp only [if_pos hν]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (col_or_le n t) (by split_ifs <;> positivity)
      · simp only [if_neg hν]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (col_coord_le n hn t) (by split_ifs <;> assumption)
    have hS := prod_schur n μ m hm0 R C hrow hcol
      (fun y c => gbK g h n (periodicLatticeShift y ν0) μ c - gbK g h n y μ c)
      (fun y c => gbK_shift_le hg hh hdvd μ ν0 y c) W
    have hdiff : ∀ y : PeriodicLatticeSite L, gbondE g h n W (periodicLatticeShift y ν0, μ) - gbondE g h n W (y, μ)
        = ∑ c : CoarseBond L n, (gbK g h n (periodicLatticeShift y ν0) μ c - gbK g h n y μ c) • W c := by
      intro y
      simp only [gbondE, ← Finset.sum_sub_distrib, sub_smul]
    simp only [hdiff]
    refine hS.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun c _ => sq_nonneg _)))
    -- (Π R)(Π C) ≤ G n
    rw [Fintype.prod_eq_mul_prod_compl ν0, Fintype.prod_eq_mul_prod_compl ν0]
    have hRo : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), R ν = ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh) := by
      refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ ν0 := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      simp only [hR, if_neg hne]
    have hCo : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), C ν
        = (∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh)) * (n : ℝ) ^ 2 := by
      rw [show (n : ℝ) ^ 2 = ∏ _ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (n : ℝ) by
        rw [Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ ν0 := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      simp only [hC, if_neg hne]
    rw [hRo, hCo]
    simp only [hR, hC, if_pos rfl]
    have hsq : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh) ^ 2
        = (∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh)) ^ 2 := by
      rw [Finset.prod_pow]
    have hGμ := hG μ
    rw [hsq] at hGμ
    set P := ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then Fg else Fh)
    set Dv := (if ν0 = μ then Dg else Dh)
    have e : 2 * Dv / n * 2 * P * (2 * Dv / n * (n + 1) * (P * (n : ℝ) ^ 2)) = 8 * Dv ^ 2 * (n + 1) * P ^ 2 := by
      field_simp; ring
    rw [show 2 * Dv / ↑n * 2 * P * (2 * Dv / ↑n * (↑n + 1) * (P * ↑n ^ 2))
        = 2 * Dv / ↑n * 2 * P * (2 * Dv / ↑n * (↑n + 1) * (P * ↑n ^ 2)) from rfl]
    calc 2 * Dv / ↑n * 2 * P * (2 * Dv / ↑n * (↑n + 1) * (P * ↑n ^ 2)) = 8 * Dv ^ 2 * (n + 1) * P ^ 2 := e
      _ ≤ G * n := hGμ
  calc ∑ b : Bond L, ‖gbondE g h n W (periodicLatticeShift b.1 ν0, b.2) - gbondE g h n W b‖ ^ 2
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L,
          ‖gbondE g h n W (periodicLatticeShift y ν0, μ) - gbondE g h n W (y, μ)‖ ^ 2 := by
        rw [Fintype.sum_prod_type_right]
    _ ≤ ∑ μ : Fin 3, G * n * ∑ c : CoarseBond L n, ‖(if c.2 = μ then W c else 0)‖ ^ 2 :=
        Finset.sum_le_sum (fun μ _ => hμ μ)
    _ = G * n * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
        rw [← Finset.mul_sum, sum_dir_split]

/-! ## the smooth instance -/

theorem sbondE_norm_sq (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖sbondE n W b‖ ^ 2 ≤ (9 * (3 / 2) ^ 2) ^ 2 * (n : ℝ) ^ 3 * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 :=
  gbondE_norm_sq (sprof_tprof n hn) (sprof_pprof n hn) hdvd W

theorem sbondE_grad_sq (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (ν0 : Fin 3) (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖sbondE n W (periodicLatticeShift b.1 ν0, b.2) - sbondE n W b‖ ^ 2
      ≤ 419904 * n * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  refine gbondE_grad_sq (sprof_tprof n hn) (sprof_pprof n hn) hdvd ν0 419904 (fun μ => ?_) W
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Finset.prod_pow]
  have hall : ∏ ν : Fin 3, (if ν = μ then (9 : ℝ) else 3 / 2) = 81 / 4 := by
    rw [Fin.prod_univ_three]; fin_cases μ <;> simp <;> norm_num
  have hsplit : ∏ ν : Fin 3, (if ν = μ then (9 : ℝ) else 3 / 2)
      = (if ν0 = μ then (9 : ℝ) else 3 / 2) * ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (9 : ℝ) else 3 / 2) :=
    Fintype.prod_eq_mul_prod_compl ν0 _
  rw [hall] at hsplit
  by_cases h : ν0 = μ
  · rw [if_pos h] at hsplit
    have hP : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (9 : ℝ) else 3 / 2) = 9 / 4 := by linarith
    rw [if_pos h, hP]; nlinarith
  · rw [if_neg h] at hsplit
    have hP : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (9 : ℝ) else 3 / 2) = 27 / 2 := by linarith
    rw [if_neg h, hP]; nlinarith

#print axioms row_eqlast_le
#print axioms col_or_le
#print axioms row_or_le
#print axioms prod_schur
#print axioms sum_dir_split
#print axioms abs_gfac_le
#print axioms gbondE_norm_sq
#print axioms shift_val_sub
#print axioms gbK_shift_le
#print axioms gbondE_grad_sq
#print axioms sbondE_norm_sq
#print axioms sbondE_grad_sq

end AdalyFormal.DLayer
