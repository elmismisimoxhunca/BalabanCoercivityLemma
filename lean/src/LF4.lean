import FE3
import LF1

/-!
# LF4 -- the tensor extension with exact cell means and gradient energy `≤ C n ε` (single stratum, any torus)

Fine torus `L` with `L μ + 1 = Nu μ * n`.  Corners = sites with `n ∣ y μ` for all `μ` (`OnLatN n y`).
* `ext3 n Nu w (x) = Σ_y (∏_μ K1(x_μ, y_μ)) • w y`, `K1(s,a) = [n ∣ a] kk((s - a))` (LF1 kernel).
* `ext3_block_sum`: `Σ_{x ∈ blockOf c n} ext3 w x = n³ • w c` for every corner `c`.
* `epsN n w = Σ_μ Σ_{corners y} ‖w (coarseShift y n μ) - w y‖²` (the cell-edge energy of the corner values).
* `ext3_grad`: `‖D_1 (ext3 w)‖² ≤ 2286144 · n · epsN n w` (`2286144 = 4·756²`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (SiteL2 gradL2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf inBlock Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.FlatExt (chi chi_nonneg row_chi_le col_chi_le schur abs_prod3_update_sub abs_prod_le_prod
  gradL2_trivial_apply pos_of_neZero_eq_mul)

variable {L : PeriodicLatticeExtent}

/-- corners of the `n`-grid. -/
def OnLatN (n : ℕ) (y : PeriodicLatticeSite L) : Prop := ∀ μ : Fin 3, n ∣ (y μ).val

instance (n : ℕ) (y : PeriodicLatticeSite L) : Decidable (OnLatN n y) := by
  unfold OnLatN; infer_instance

/-- 1D factor and its majorant. -/
noncomputable def K1 (n Nu : ℕ) {N : ℕ} (s a : Fin N) : ℝ := if n ∣ a.val then kk n Nu (s - a).val else 0
noncomputable def X1 (n Nu : ℕ) {N : ℕ} (s a : Fin N) : ℝ := if n ∣ a.val then chi n Nu (s - a).val else 0

noncomputable def ker3 (n : ℕ) (Nu : Fin 3 → ℕ) (x y : PeriodicLatticeSite L) : ℝ :=
  ∏ μ : Fin 3, K1 n (Nu μ) (x μ) (y μ)
noncomputable def maj3 (n : ℕ) (Nu : Fin 3 → ℕ) (x y : PeriodicLatticeSite L) : ℝ :=
  ∏ μ : Fin 3, X1 n (Nu μ) (x μ) (y μ)

/-- **the extension**. -/
noncomputable def ext3 (n : ℕ) (Nu : Fin 3 → ℕ) (w : PeriodicLatticeSite L → SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun x => ∑ y, ker3 n Nu x y • w y)

theorem ext3_apply (n : ℕ) (Nu : Fin 3 → ℕ) (w : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) :
    (ext3 n Nu w).ofLp x = ∑ y, ker3 n Nu x y • w y := rfl

/-- the cell-edge energy. -/
noncomputable def epsMu (n : ℕ) (w : PeriodicLatticeSite L → SuTwo) (μ : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, if OnLatN n y then ‖w (coarseShift y n μ) - w y‖ ^ 2 else 0

noncomputable def epsN (n : ℕ) (w : PeriodicLatticeSite L → SuTwo) : ℝ := ∑ μ : Fin 3, epsMu n w μ

section hyp
variable (n : ℕ) (Nu : Fin 3 → ℕ) (hn : 0 < n) (hN : ∀ μ : Fin 3, L μ + 1 = Nu μ * n)
include hn hN

theorem X1_nonneg {N0 : ℕ} (s a : Fin N0) (m : ℕ) : 0 ≤ X1 n m s a := by
  unfold X1; split_ifs
  · exact chi_nonneg _ _ _
  · exact le_refl 0

theorem abs_K1_le (μ : Fin 3) (s a : Fin (L μ + 1)) : |K1 n (Nu μ) s a| ≤ 2 * X1 n (Nu μ) s a := by
  unfold K1 X1; split_ifs
  · exact abs_kk_le n (Nu μ) _ hn
  · simp

theorem abs_K1_step (μ : Fin 3) (s a : Fin (L μ + 1)) :
    |K1 n (Nu μ) (s + 1) a - K1 n (Nu μ) s a| ≤ 7 / n * X1 n (Nu μ) s a := by
  unfold K1 X1
  split_ifs with h
  · have hNu : 0 < Nu μ := pos_of_neZero_eq_mul (hN μ)
    have he : s + 1 - a = (s - a) + 1 := by abel
    have hv : (s + 1 - a).val = ((s - a).val + 1) % (L μ + 1) := by
      rw [he, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    have hv2 : ((s - a).val + 1) % (L μ + 1) = ((s - a).val + 1) % (Nu μ * n) :=
      congrArg (fun m => ((s - a).val + 1) % m) (hN μ)
    rw [hv, hv2]
    have hlt : (s - a).val < Nu μ * n := by have := (s - a).isLt; rw [← hN μ]; exact this
    exact abs_kk_step n (Nu μ) _ hn hNu hlt
  · simp

theorem K1_partition (μ : Fin 3) (s : Fin (L μ + 1)) : ∑ a, K1 n (Nu μ) s a = 1 :=
  kk_partition (Nu μ) n hn (hN μ) s

theorem K1_block (μ : Fin 3) (c a : Fin (L μ + 1)) (hc : n ∣ c.val) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin (L μ + 1) => c.val ≤ s.val ∧ s.val < c.val + n), K1 n (Nu μ) s a
      = if a = c then (n : ℝ) else 0 := by
  unfold K1
  by_cases ha : n ∣ a.val
  · simp only [ha, if_true]
    rw [kk_block_mean (Nu μ) n hn (hN μ) a c ha hc]
    by_cases hac : a = c
    · subst hac; simp
    · rw [if_neg (Ne.symm hac), if_neg hac]
  · simp only [ha, if_false, Finset.sum_const_zero]
    have : a ≠ c := fun h => ha (h ▸ hc)
    rw [if_neg this]

theorem blockOf_pi (c : PeriodicLatticeSite L) :
    blockOf c n = Fintype.piFinset (fun μ => Finset.univ.filter
      (fun a : Fin (L μ + 1) => (c μ).val ≤ a.val ∧ a.val < (c μ).val + n)) := by
  ext x
  simp only [mem_blockOf, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, inBlock]

theorem ker3_block (c y : PeriodicLatticeSite L) (hc : OnLatN n c) :
    ∑ x ∈ blockOf c n, ker3 n Nu x y = if y = c then ((n : ℝ)) ^ 3 else 0 := by
  classical
  rw [blockOf_pi n Nu hn hN c]
  unfold ker3
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (L μ + 1)) => K1 n (Nu μ) a (y μ))).symm.trans ?_
  rw [Finset.prod_congr rfl (fun μ _ => K1_block n Nu hn hN μ (c μ) (y μ) (hc μ)), Finset.prod_ite_zero]
  have hiff : (∀ μ ∈ (Finset.univ : Finset (Fin 3)), y μ = c μ) ↔ y = c :=
    ⟨fun h => funext fun μ => h μ (Finset.mem_univ μ), fun h μ _ => h ▸ rfl⟩
  simp only [hiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **exact cell means**. -/
theorem ext3_block_sum (w : PeriodicLatticeSite L → SuTwo) (c : PeriodicLatticeSite L) (hc : OnLatN n c) :
    ∑ x ∈ blockOf c n, (ext3 n Nu w).ofLp x = ((n : ℝ) ^ 3) • w c := by
  classical
  simp only [ext3_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hk := fun y => ker3_block n Nu hn hN c y hc
  simp only [hk, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ker3_partition (x : PeriodicLatticeSite L) : ∑ y, ker3 n Nu x y = 1 := by
  classical
  unfold ker3
  rw [← Fintype.piFinset_univ]
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (L μ + 1)) => K1 n (Nu μ) (x μ) a)).symm.trans ?_
  rw [Finset.prod_congr rfl (fun μ _ => K1_partition n Nu hn hN μ (x μ)), Finset.prod_const_one]

end hyp

/-! ## splitting a site sum along one coordinate -/

theorem sum_update_split {E : Type*} [AddCommMonoid E] (μ : Fin 3) (c : Fin (L μ + 1))
    (f : PeriodicLatticeSite L → E) :
    ∑ y, f y = ∑ a : Fin (L μ + 1), ∑ y' ∈ Finset.univ.filter (fun y' : PeriodicLatticeSite L => y' μ = c),
      f (Function.update y' μ a) := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun y => (y μ, Function.update y μ c)) (fun p => Function.update p.2 μ p.1)
    ?_ ?_ ?_ ?_ ?_
  · intro y _; simp
  · intro p _; simp
  · intro y _; simp
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
    refine Prod.ext (by simp) ?_
    simp only [Function.update_idem]
    rw [← hp]; exact Function.update_eq_self μ p.2
  · intro y _; simp

theorem sum_mu_cancel {E : Type*} [AddCommGroup E] [Module ℝ E] (μ : Fin 3) (G : Fin (L μ + 1) → ℝ)
    (hG : ∑ a, G a = 0) (F : PeriodicLatticeSite L → E) (hF : ∀ y a, F (Function.update y μ a) = F y) :
    ∑ y, G (y μ) • F y = 0 := by
  classical
  rw [sum_update_split μ 0]
  have hrow : ∀ a : Fin (L μ + 1), ∑ y' ∈ Finset.univ.filter (fun y' : PeriodicLatticeSite L => y' μ = 0),
      G ((Function.update y' μ a) μ) • F (Function.update y' μ a)
      = G a • ∑ y' ∈ Finset.univ.filter (fun y' : PeriodicLatticeSite L => y' μ = 0), F y' := by
    intro a
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [Function.update_self, hF]
  rw [Finset.sum_congr rfl (fun a _ => hrow a), ← Finset.sum_smul, hG, zero_smul]

/-! ## the gradient -/

theorem gradL2_flat_apply (f : SiteL2 L) (b : Bond L) :
    (gradL2 (trivialU L) f).ofLp b = f.ofLp (periodicLatticeShift b.1 b.2) - f.ofLp b.1 :=
  gradL2_trivial_apply f b

/-- full loop. -/
theorem coarseShift_full (y : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift y (L μ + 1) μ = y := by
  funext ν
  by_cases h : ν = μ
  · subst h; apply Fin.ext; rw [coarseShift_val_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (y ν).isLt]
  · exact coarseShift_apply_ne y _ μ ν h

theorem coarseShift_add (y : PeriodicLatticeSite L) (a b : ℕ) (μ : Fin 3) :
    coarseShift (coarseShift y a μ) b μ = coarseShift y (a + b) μ := by
  unfold coarseShift
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-- the corner coordinate of `s`. -/
def cornerC (n : ℕ) {N : ℕ} (s : Fin N) : Fin N :=
  ⟨n * (s.val / n), lt_of_le_of_lt (Nat.mul_div_le s.val n) s.isLt⟩

theorem periodicLatticeShift_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    periodicLatticeShift x μ ν = x ν := by
  simp [periodicLatticeShift, Function.update_of_ne h]

theorem periodicLatticeShift_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift x μ μ = x μ + 1 := by
  simp [periodicLatticeShift]

section grad
variable (n : ℕ) (Nu : Fin 3 → ℕ) (hn : 0 < n) (hN : ∀ μ : Fin 3, L μ + 1 = Nu μ * n)
include hn hN

/-- the kernel difference factorises through coordinate `μ`. -/
theorem ker3_diff (x y : PeriodicLatticeSite L) (μ : Fin 3) :
    ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y
      = (K1 n (Nu μ) (x μ + 1) (y μ) - K1 n (Nu μ) (x μ) (y μ))
        * ∏ ν ∈ Finset.univ.erase μ, K1 n (Nu ν) (x ν) (y ν) := by
  unfold ker3
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ),
    ← Finset.mul_prod_erase Finset.univ (fun ν => K1 n (Nu ν) (x ν) (y ν)) (Finset.mem_univ μ)]
  rw [periodicLatticeShift_self]
  have : ∏ ν ∈ Finset.univ.erase μ, K1 n (Nu ν) (periodicLatticeShift x μ ν) (y ν)
      = ∏ ν ∈ Finset.univ.erase μ, K1 n (Nu ν) (x ν) (y ν) :=
    Finset.prod_congr rfl (fun ν hν => by rw [periodicLatticeShift_ne x μ ν (Finset.ne_of_mem_erase hν)])
  rw [this]; ring

/-- the reference cancels: `Σ_y (ker3 x⁺ y - ker3 x y) • w(y with μ-coordinate := corner of x) = 0`. -/
theorem ker3_diff_cancel (w : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ y, (ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y) • w (Function.update y μ (cornerC n (x μ))) = 0 := by
  have hk : ∀ y, ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y
      = (K1 n (Nu μ) (x μ + 1) (y μ) - K1 n (Nu μ) (x μ) (y μ))
        * ∏ ν ∈ Finset.univ.erase μ, K1 n (Nu ν) (x ν) (y ν) := fun y => ker3_diff n Nu hn hN x y μ
  simp_rw [hk, mul_smul]
  refine sum_mu_cancel μ (fun a => K1 n (Nu μ) (x μ + 1) a - K1 n (Nu μ) (x μ) a) ?_
    (fun y => (∏ ν ∈ Finset.univ.erase μ, K1 n (Nu ν) (x ν) (y ν)) • w (Function.update y μ (cornerC n (x μ)))) ?_
  · rw [Finset.sum_sub_distrib, K1_partition n Nu hn hN, K1_partition n Nu hn hN, sub_self]
  · intro y a
    congr 1
    · refine Finset.prod_congr rfl (fun ν hν => ?_)
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]
    · rw [Function.update_idem]

theorem abs_ker3_diff_le (x y : PeriodicLatticeSite L) (μ : Fin 3) :
    |ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y| ≤ 28 / n * maj3 n Nu x y := by
  have h := abs_prod3_update_sub (fun ν => K1 n (Nu ν) (x ν) (y ν))
    (fun ν => K1 n (Nu ν) (periodicLatticeShift x μ ν) (y ν)) (fun ν => 2 * X1 n (Nu ν) (x ν) (y ν)) μ
    (7 / 2 / n) (by positivity)
    (fun ν hν => by simp only [periodicLatticeShift_ne x μ ν hν])
    (fun ν => abs_K1_le n Nu hn hN ν _ _)
    (by
      simp only [periodicLatticeShift_self]
      have := abs_K1_step n Nu hn hN μ (x μ) (y μ)
      have e : 7 / 2 / (n : ℝ) * (2 * X1 n (Nu μ) (x μ) (y μ)) = 7 / n * X1 n (Nu μ) (x μ) (y μ) := by ring
      rw [e]; exact this)
  unfold ker3 maj3
  have e2 : ∏ ν : Fin 3, 2 * X1 n (Nu ν) (x ν) (y ν) = 8 * ∏ ν : Fin 3, X1 n (Nu ν) (x ν) (y ν) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; norm_num
  rw [e2] at h
  calc _ ≤ 7 / 2 / (n : ℝ) * (8 * ∏ ν : Fin 3, X1 n (Nu ν) (x ν) (y ν)) := h
    _ = 28 / n * ∏ ν : Fin 3, X1 n (Nu ν) (x ν) (y ν) := by ring

theorem maj3_nonneg (x y : PeriodicLatticeSite L) : 0 ≤ maj3 n Nu x y :=
  Finset.prod_nonneg (fun ν _ => X1_nonneg n Nu hn hN _ _ _)

theorem row_maj3_le (x : PeriodicLatticeSite L) : ∑ y, maj3 n Nu x y ≤ 27 := by
  classical
  unfold maj3
  rw [← Fintype.piFinset_univ]
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (L μ + 1)) => X1 n (Nu μ) (x μ) a)).symm.trans_le ?_
  calc ∏ μ : Fin 3, ∑ a ∈ (Finset.univ : Finset (Fin (L μ + 1))), X1 n (Nu μ) (x μ) a
      ≤ ∏ _μ : Fin 3, (3 : ℝ) := by
        refine Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun a _ => X1_nonneg n Nu hn hN _ _ _))
          (fun μ _ => ?_)
        have hd : n ∣ L μ + 1 := ⟨Nu μ, by rw [hN μ, Nat.mul_comm]⟩
        exact row_chi_le n (Nu μ) hd (x μ)
    _ = 27 := by norm_num [Finset.prod_const]

theorem col_maj3_le (y : PeriodicLatticeSite L) : ∑ x, maj3 n Nu x y ≤ 27 * (n : ℝ) ^ 3 := by
  classical
  unfold maj3
  rw [← Fintype.piFinset_univ]
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (L μ + 1)) => X1 n (Nu μ) a (y μ))).symm.trans_le ?_
  calc ∏ μ : Fin 3, ∑ a ∈ (Finset.univ : Finset (Fin (L μ + 1))), X1 n (Nu μ) a (y μ)
      ≤ ∏ _μ : Fin 3, (3 * (n : ℝ)) := by
        refine Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun a _ => X1_nonneg n Nu hn hN _ _ _))
          (fun μ _ => ?_)
        calc ∑ a ∈ (Finset.univ : Finset (Fin (L μ + 1))), X1 n (Nu μ) a (y μ)
            ≤ ∑ a : Fin (L μ + 1), chi n (Nu μ) (a - y μ).val := by
              refine Finset.sum_le_sum (fun a _ => ?_)
              unfold X1; split_ifs
              · exact le_refl _
              · exact chi_nonneg _ _ _
          _ ≤ 3 * n := col_chi_le n (Nu μ) hn (y μ)
    _ = 27 * (n : ℝ) ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

/-- the backward `n`-shift. -/
noncomputable def backN (μ : Fin 3) (y : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  coarseShift y (L μ + 1 - n) μ

theorem shift_backN (μ : Fin 3) (y : PeriodicLatticeSite L) : coarseShift (backN n μ y) n μ = y := by
  unfold backN
  have hle : n ≤ L μ + 1 := by rw [hN μ]; exact Nat.le_mul_of_pos_left n (pos_of_neZero_eq_mul (hN μ))
  rw [coarseShift_add, Nat.sub_add_cancel hle, coarseShift_full]

theorem backN_shift (μ : Fin 3) (y : PeriodicLatticeSite L) : backN n μ (coarseShift y n μ) = y := by
  unfold backN
  have hle : n ≤ L μ + 1 := by rw [hN μ]; exact Nat.le_mul_of_pos_left n (pos_of_neZero_eq_mul (hN μ))
  rw [coarseShift_add, Nat.add_sub_cancel' hle, coarseShift_full]

theorem onLat_coarseShift (μ : Fin 3) (y : PeriodicLatticeSite L) (m : ℕ) (hm : n ∣ m) (hy : OnLatN n y) :
    OnLatN n (coarseShift y m μ) := by
  intro ν
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq]
    have hd : n ∣ L ν + 1 := ⟨Nu ν, by rw [hN ν, Nat.mul_comm]⟩
    exact (Nat.dvd_mod_iff hd).mpr (Nat.dvd_add (hy ν) hm)
  · rw [coarseShift_apply_ne y m μ ν h]; exact hy ν

theorem onLat_backN (μ : Fin 3) (y : PeriodicLatticeSite L) (hy : OnLatN n y) : OnLatN n (backN n μ y) := by
  unfold backN
  have hd : n ∣ L μ + 1 := ⟨Nu μ, by rw [hN μ, Nat.mul_comm]⟩
  have hle : n ≤ L μ + 1 := Nat.le_of_dvd (Nat.succ_pos _) hd
  exact onLat_coarseShift n Nu hn hN μ y _ (Nat.dvd_sub hd (dvd_refl n)) hy

/-- the shift-difference bound: for a corner `y` interacting with `x`, `w y - w(y with μ := corner)` is one edge. -/
theorem diff_le_edges (w : PeriodicLatticeSite L → SuTwo) (x y : PeriodicLatticeSite L) (μ : Fin 3)
    (hy : OnLatN n y) (hX : X1 n (Nu μ) (x μ) (y μ) ≠ 0) :
    ‖w y - w (Function.update y μ (cornerC n (x μ)))‖
      ≤ ‖w (coarseShift y n μ) - w y‖ + ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖ := by
  have hchi : chi n (Nu μ) (x μ - y μ).val ≠ 0 := by
    unfold X1 at hX; rwa [if_pos (hy μ)] at hX
  have hc := chi_corner (Nu μ) n hn (hN μ) (x μ) (y μ) (hy μ) hchi
  have hN' := hN μ
  have hpos : 0 < L μ + 1 := Nat.succ_pos _
  have hcv : (cornerC n (x μ)).val = n * ((x μ).val / n) := rfl
  have hcl : n * ((x μ).val / n) < L μ + 1 := (cornerC n (x μ)).isLt
  rcases hc with h0 | h1 | h2
  · have : Function.update y μ (cornerC n (x μ)) = y := by
      rw [Function.update_eq_iff]; exact ⟨Fin.ext (by rw [hcv, h0]), fun _ _ => rfl⟩
    rw [this, sub_self, norm_zero]; positivity
  · -- y μ = corner + n: update y μ corner = backN y
    have hb : Function.update y μ (cornerC n (x μ)) = backN n μ y := by
      unfold backN
      funext ν
      by_cases hν : ν = μ
      · subst hν
        rw [Function.update_self]
        apply Fin.ext
        rw [coarseShift_val_eq, hcv, h1]
        have hle : n ≤ L ν + 1 := by rw [hN']; exact Nat.le_mul_of_pos_left n (pos_of_neZero_eq_mul hN')
        rw [Nat.mod_add_mod, show n * ((x ν).val / n) + n + (L ν + 1 - n) = n * ((x ν).val / n) + (L ν + 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hcl]
      · rw [Function.update_of_ne hν, coarseShift_apply_ne y _ μ ν hν]
    rw [hb, shift_backN n Nu hn hN μ y]
    have := norm_nonneg (w (coarseShift y n μ) - w y)
    linarith
  · -- corner = y μ + n: coarseShift y n = update y μ corner
    have hs : coarseShift y n μ = Function.update y μ (cornerC n (x μ)) := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        rw [Function.update_self]
        apply Fin.ext
        rw [coarseShift_val_eq, hcv, h2]
      · rw [Function.update_of_ne hν, coarseShift_apply_ne y _ μ ν hν]
    rw [← hs, norm_sub_rev]
    have := norm_nonneg (w (coarseShift (backN n μ y) n μ) - w (backN n μ y))
    linarith

/-- the gated edge weight. -/
noncomputable def aEdge (w : PeriodicLatticeSite L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  if OnLatN n y then ‖w (coarseShift y n μ) - w y‖ + ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖
  else 0

theorem aEdge_nonneg (w : PeriodicLatticeSite L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) :
    0 ≤ aEdge n w μ y := by
  unfold aEdge; split_ifs <;> positivity

theorem pointwise_grad (w : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ‖(ext3 n Nu w).ofLp (periodicLatticeShift x μ) - (ext3 n Nu w).ofLp x‖
      ≤ ∑ y, (28 / n * maj3 n Nu x y) * aEdge n w μ y := by
  simp only [ext3_apply]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  have hcan := ker3_diff_cancel n Nu hn hN w x μ
  have e : ∑ y, (ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y) • w y
      = ∑ y, (ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y) • (w y - w (Function.update y μ (cornerC n (x μ)))) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hcan, sub_zero]
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun y _ => ?_))
  rw [norm_smul, Real.norm_eq_abs]
  have hab := abs_ker3_diff_le n Nu hn hN x y μ
  by_cases hm : maj3 n Nu x y = 0
  · have : |ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y| = 0 := by
      have := abs_nonneg (ker3 n Nu (periodicLatticeShift x μ) y - ker3 n Nu x y)
      rw [hm, mul_zero] at hab; linarith
    rw [this, zero_mul]
    exact mul_nonneg (by have := maj3_nonneg n Nu hn hN x y; positivity) (aEdge_nonneg n Nu hn hN w μ y)
  · -- every factor of maj3 is nonzero, so `y` is a corner and `X1 μ ≠ 0`
    have hall : ∀ ν, X1 n (Nu ν) (x ν) (y ν) ≠ 0 := by
      intro ν hν; apply hm; unfold maj3; exact Finset.prod_eq_zero (Finset.mem_univ ν) hν
    have hy : OnLatN n y := by
      intro ν; have := hall ν; unfold X1 at this; by_contra hc; rw [if_neg hc] at this; exact this rfl
    have hd := diff_le_edges n Nu hn hN w x y μ hy (hall μ)
    unfold aEdge; rw [if_pos hy]
    exact mul_le_mul hab hd (norm_nonneg _) (by have := maj3_nonneg n Nu hn hN x y; positivity)

theorem sum_aEdge_sq (w : PeriodicLatticeSite L → SuTwo) (μ : Fin 3) :
    ∑ y, aEdge n w μ y ^ 2 ≤ 4 * epsMu n w μ := by
  have h1 : ∀ y, aEdge n w μ y ^ 2 ≤
      2 * (if OnLatN n y then ‖w (coarseShift y n μ) - w y‖ ^ 2 else 0)
      + 2 * (if OnLatN n (backN n μ y) then
          ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖ ^ 2 else 0) := by
    intro y
    unfold aEdge
    by_cases hy : OnLatN n y
    · rw [if_pos hy, if_pos hy, if_pos (onLat_backN n Nu hn hN μ y hy)]
      nlinarith [sq_nonneg (‖w (coarseShift y n μ) - w y‖ -
        ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖)]
    · rw [if_neg hy, if_neg hy]
      have : 0 ≤ (if OnLatN n (backN n μ y) then
          ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖ ^ 2 else 0) := by
        split_ifs <;> positivity
      nlinarith
  have hbij : ∑ y, (if OnLatN n (backN n μ y) then
        ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖ ^ 2 else 0)
      = epsMu n w μ := by
    unfold epsMu
    exact Fintype.sum_bijective (backN n μ)
      ⟨fun a b h => by rw [← shift_backN n Nu hn hN μ a, h, shift_backN n Nu hn hN μ b],
       fun z => ⟨coarseShift z n μ, backN_shift n Nu hn hN μ z⟩⟩ _ _ (fun y => rfl)
  calc ∑ y, aEdge n w μ y ^ 2
      ≤ ∑ y, (2 * (if OnLatN n y then ‖w (coarseShift y n μ) - w y‖ ^ 2 else 0)
        + 2 * (if OnLatN n (backN n μ y) then
          ‖w (coarseShift (backN n μ y) n μ) - w (backN n μ y)‖ ^ 2 else 0)) :=
        Finset.sum_le_sum (fun y _ => h1 y)
    _ = 2 * epsMu n w μ + 2 * epsMu n w μ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hbij]; rfl
    _ = 4 * epsMu n w μ := by ring

/-- **gradient energy of the extension**. -/
theorem ext3_grad (w : PeriodicLatticeSite L → SuTwo) :
    ‖gradL2 (trivialU L) (ext3 n Nu w)‖ ^ 2 ≤ 2286144 * n * epsN n w := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [gradL2_flat_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold epsN
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have hsch := schur (fun x y => 28 / (n : ℝ) * maj3 n Nu x y) (fun x y => 28 / (n : ℝ) * maj3 n Nu x y)
    (fun x y => by rw [abs_of_nonneg (by have := maj3_nonneg n Nu hn hN x y; positivity)])
    (28 / (n : ℝ) * 27) (28 / (n : ℝ) * (27 * (n : ℝ) ^ 3)) (by positivity)
    (fun x => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (row_maj3_le n Nu hn hN x) (by positivity))
    (fun y => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (col_maj3_le n Nu hn hN y) (by positivity))
    (fun y => aEdge n w μ y)
  have hpt : ∀ x, ‖(ext3 n Nu w).ofLp (periodicLatticeShift x μ) - (ext3 n Nu w).ofLp x‖ ^ 2
      ≤ ‖∑ y, (28 / (n : ℝ) * maj3 n Nu x y) • aEdge n w μ y‖ ^ 2 := by
    intro x
    have h1 := pointwise_grad n Nu hn hN w x μ
    have h0 : 0 ≤ ∑ y, (28 / (n : ℝ) * maj3 n Nu x y) * aEdge n w μ y :=
      Finset.sum_nonneg (fun y _ => mul_nonneg (by have := maj3_nonneg n Nu hn hN x y; positivity)
        (aEdge_nonneg n Nu hn hN w μ y))
    have e : ‖∑ y, (28 / (n : ℝ) * maj3 n Nu x y) • aEdge n w μ y‖
        = ∑ y, (28 / (n : ℝ) * maj3 n Nu x y) * aEdge n w μ y := by
      simp only [smul_eq_mul]; rw [Real.norm_eq_abs, abs_of_nonneg h0]
    rw [e]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsq : ∑ y, ‖aEdge n w μ y‖ ^ 2 ≤ 4 * epsMu n w μ := by
    have := sum_aEdge_sq n Nu hn hN w μ
    simpa [Real.norm_eq_abs, sq_abs] using this
  calc ∑ x, ‖(ext3 n Nu w).ofLp (periodicLatticeShift x μ) - (ext3 n Nu w).ofLp x‖ ^ 2
      ≤ ∑ x, ‖∑ y, (28 / (n : ℝ) * maj3 n Nu x y) • aEdge n w μ y‖ ^ 2 := Finset.sum_le_sum (fun x _ => hpt x)
    _ ≤ 28 / (n : ℝ) * 27 * (28 / (n : ℝ) * (27 * (n : ℝ) ^ 3)) * ∑ y, ‖aEdge n w μ y‖ ^ 2 := hsch
    _ ≤ 28 / (n : ℝ) * 27 * (28 / (n : ℝ) * (27 * (n : ℝ) ^ 3)) * (4 * epsMu n w μ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2286144 * n * epsMu n w μ := by field_simp; ring

end grad

#print axioms ker3_block
#print axioms ext3_block_sum
#print axioms ker3_partition
#print axioms sum_update_split
#print axioms sum_mu_cancel
#print axioms ker3_diff_cancel
#print axioms abs_ker3_diff_le
#print axioms diff_le_edges
#print axioms pointwise_grad
#print axioms sum_aEdge_sq
#print axioms ext3_grad

#print axioms ext3_apply
#print axioms X1_nonneg
#print axioms abs_K1_le
#print axioms abs_K1_step
#print axioms K1_partition
#print axioms K1_block
#print axioms blockOf_pi
#print axioms gradL2_flat_apply
#print axioms coarseShift_full
#print axioms coarseShift_add
#print axioms periodicLatticeShift_ne
#print axioms periodicLatticeShift_self
#print axioms ker3_diff
#print axioms maj3_nonneg
#print axioms row_maj3_le
#print axioms col_maj3_le
#print axioms shift_backN
#print axioms backN_shift
#print axioms onLat_coarseShift
#print axioms onLat_backN
#print axioms aEdge_nonneg

end AdalyFormal.LemIFlat
