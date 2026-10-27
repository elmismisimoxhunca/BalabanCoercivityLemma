import MS4

/-!
# MS5 -- S3 part 2: face counting and the gradient energy of a block-constant field

For a block `B = B(y, n)` that fits in the torus (`y_μ + n ≤ L_μ + 1`, no wrap):
* `card_blockOf` : `|B| = n³`;  `face_card` : `|{x ∈ B : x_μ = t}| ≤ n²`;
* `exit_top` / `enter_bottom` : a bond leaving `B` in direction `μ` starts on the top face, a bond entering `B` ends on the
  bottom face;  `sum_out_le` / `sum_in_le` : at most `3n²` bonds leave (enter) `B`;  `card_inBlockBonds_le` : `≤ 3n³` in-block bonds.
* **`grad_blockconst_le`** : if `G = Σ_i c_i 1_{B_i}` on pairwise disjoint fitting blocks `B_i = B(y_i, n_i)` (and `0` elsewhere), and
  every in-block link of `B_i` has `‖U_b − 1‖_F ≤ δ_i`, then `‖D_U G‖² ≤ Σ_i (12 δ_i² n_i³ + 12 n_i²) ‖c_i‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem shift_apply_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = if x μ = Fin.last (L μ) then 0 else (x μ).val + 1 := by
  simp only [periodicLatticeShift, Function.update_self]
  exact Fin.val_add_one (x μ)

theorem shift_apply_ne (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν := by
  simp only [periodicLatticeShift, Function.update_of_ne h]

theorem exit_top {y x : PeriodicLatticeSite L} {n : ℕ} (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)
    (hx : x ∈ blockOf y n) (μ : Fin 3) (hout : periodicLatticeShift x μ ∉ blockOf y n) :
    (x μ).val + 1 = (y μ).val + n := by
  rw [mem_blockOf] at hx
  by_contra hne
  apply hout
  rw [mem_blockOf]
  intro ν
  by_cases hν : ν = μ
  · subst hν
    have h1 := hx ν
    have hfν := hfit ν
    have hnl : x ν ≠ Fin.last (L ν) := by
      intro h; rw [h, Fin.val_last] at h1 hne; omega
    rw [shift_apply_self, if_neg hnl]
    omega
  · rw [shift_apply_ne x hν]; exact hx ν

theorem enter_bottom {y x : PeriodicLatticeSite L} {n : ℕ} {μ : Fin 3}
    (hin : periodicLatticeShift x μ ∈ blockOf y n) (hx : x ∉ blockOf y n) :
    ((periodicLatticeShift x μ) μ).val = (y μ).val := by
  rw [mem_blockOf] at hin
  by_contra hne
  apply hx
  rw [mem_blockOf]
  intro ν
  by_cases hν : ν = μ
  · subst hν
    have h1 := hin ν
    rw [shift_apply_self] at h1 hne
    split_ifs at h1 hne with hl
    · omega
    · omega
  · have := hin ν; rw [shift_apply_ne x hν] at this; exact this

theorem face_card_gen (y : PeriodicLatticeSite L) (n : ℕ) (μ ν₁ ν₂ : Fin 3)
    (hcov : ∀ ν : Fin 3, ν = μ ∨ ν = ν₁ ∨ ν = ν₂) (t : ℕ) :
    ((blockOf y n).filter (fun x => (x μ).val = t)).card ≤ n * n := by
  classical
  have hmap : ∀ x ∈ (blockOf y n).filter (fun x => (x μ).val = t),
      ((x ν₁).val, (x ν₂).val) ∈ Finset.Ico (y ν₁).val ((y ν₁).val + n) ×ˢ Finset.Ico (y ν₂).val ((y ν₂).val + n) := by
    intro x hx
    rw [Finset.mem_filter, mem_blockOf] at hx
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    exact ⟨hx.1 ν₁, hx.1 ν₂⟩
  have hinj : Set.InjOn (fun x : PeriodicLatticeSite L => ((x ν₁).val, (x ν₂).val))
      ↑((blockOf y n).filter (fun x => (x μ).val = t)) := by
    intro x hx x' hx' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hx'
    have h' := Prod.mk.inj h
    funext ν
    apply Fin.ext
    rcases hcov ν with rfl | rfl | rfl
    · rw [hx.2, hx'.2]
    · exact h'.1
    · exact h'.2
  have := Finset.card_le_card_of_injOn _ (fun x hx => hmap x hx) hinj
  rw [Finset.card_product, Nat.card_Ico, Nat.card_Ico, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at this
  exact this

theorem face_card (y : PeriodicLatticeSite L) (n : ℕ) (μ : Fin 3) (t : ℕ) :
    ((blockOf y n).filter (fun x => (x μ).val = t)).card ≤ n * n := by
  fin_cases μ
  · exact face_card_gen y n 0 1 2 (fun ν => by fin_cases ν <;> simp) t
  · exact face_card_gen y n 1 0 2 (fun ν => by fin_cases ν <;> simp) t
  · exact face_card_gen y n 2 0 1 (fun ν => by fin_cases ν <;> simp) t

theorem card_out_le (y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (μ : Fin 3) :
    ((blockOf y n).filter (fun x => periodicLatticeShift x μ ∉ blockOf y n)).card ≤ n * n := by
  classical
  refine le_trans (Finset.card_le_card ?_) (face_card y n μ ((y μ).val + n - 1))
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have := exit_top hfit hx.1 μ hx.2
  omega

theorem card_in_le (y : PeriodicLatticeSite L) (n : ℕ) (μ : Fin 3) :
    (Finset.univ.filter (fun x => periodicLatticeShift x μ ∈ blockOf y n ∧ x ∉ blockOf y n)).card ≤ n * n := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun x => periodicLatticeShift x μ) ?_ ?_) (face_card y n μ (y μ).val)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hx.1, enter_bottom hx.1 hx.2⟩
  · intro x _ x' _ h
    exact shift_injective μ h

theorem card_inBlockBonds_le (y : PeriodicLatticeSite L) (n : ℕ) : (inBlockBonds y n).card ≤ 3 * n ^ 3 := by
  classical
  have hsub : inBlockBonds y n ⊆ blockOf y n ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro b hb
    rw [mem_inBlockBonds] at hb
    exact Finset.mem_product.mpr ⟨hb.1, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (blockOf y n).card ≤ n ^ 3 := by
    rw [← boxF_eq_blockOf]; exact AdalyFormal.DLayer.card_boxF_le y n
  nlinarith

theorem sum_out_le (y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (φ : ℝ) (hφ : 0 ≤ φ) :
    ∑ b : Bond L, (if b.1 ∈ blockOf y n ∧ periodicLatticeShift b.1 b.2 ∉ blockOf y n then φ else 0)
      ≤ 3 * ((n : ℝ) * n) * φ := by
  classical
  rw [Fintype.sum_prod_type_right]
  have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L,
      (if x ∈ blockOf y n ∧ periodicLatticeShift x μ ∉ blockOf y n then φ else 0) ≤ ((n : ℝ) * n) * φ := by
    intro μ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (Finset.univ.filter (fun x => x ∈ blockOf y n ∧ periodicLatticeShift x μ ∉ blockOf y n)).card
        ≤ n * n := by
      refine le_trans (le_of_eq ?_) (card_out_le y n hfit μ)
      congr 1; ext x; simp
    have : ((Finset.univ.filter (fun x => x ∈ blockOf y n ∧ periodicLatticeShift x μ ∉ blockOf y n)).card : ℝ)
        ≤ (n : ℝ) * n := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right this hφ
  have := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => hμ μ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

theorem sum_in_le (y : PeriodicLatticeSite L) (n : ℕ) (φ : ℝ) (hφ : 0 ≤ φ) :
    ∑ b : Bond L, (if periodicLatticeShift b.1 b.2 ∈ blockOf y n ∧ b.1 ∉ blockOf y n then φ else 0)
      ≤ 3 * ((n : ℝ) * n) * φ := by
  classical
  rw [Fintype.sum_prod_type_right]
  have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L,
      (if periodicLatticeShift x μ ∈ blockOf y n ∧ x ∉ blockOf y n then φ else 0) ≤ ((n : ℝ) * n) * φ := by
    intro μ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.univ.filter (fun x => periodicLatticeShift x μ ∈ blockOf y n ∧ x ∉ blockOf y n)).card : ℝ)
        ≤ (n : ℝ) * n := by exact_mod_cast card_in_le y n μ
    exact mul_le_mul_of_nonneg_right this hφ
  have := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => hμ μ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

theorem sum_inBlock_le (y : PeriodicLatticeSite L) (n : ℕ) (φ : ℝ) (hφ : 0 ≤ φ) :
    ∑ b : Bond L, (if b ∈ inBlockBonds y n then φ else 0) ≤ 3 * (n : ℝ) ^ 3 * φ := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h1 : (Finset.univ.filter (fun b => b ∈ inBlockBonds y n)) = inBlockBonds y n := by ext b; simp
  rw [h1]
  have : ((inBlockBonds y n).card : ℝ) ≤ 3 * (n : ℝ) ^ 3 := by exact_mod_cast card_inBlockBonds_le y n
  exact mul_le_mul_of_nonneg_right this hφ

/-- **gradient energy of a block-constant field** -/
theorem grad_blockconst_le {ι : Type*} [Fintype ι] (U : Cfg L) (yb : ι → PeriodicLatticeSite L) (nb : ι → ℕ)
    (hfit : ∀ i, ∀ μ, (yb i μ).val + nb i ≤ L μ + 1)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (blockOf (yb i) (nb i)) (blockOf (yb i') (nb i')))
    (c : ι → SuTwo) (Gf : SiteL2 L)
    (hon : ∀ i, ∀ x ∈ blockOf (yb i) (nb i), Gf x = c i)
    (hoff : ∀ x, (∀ i, x ∉ blockOf (yb i) (nb i)) → Gf x = 0)
    (δ : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hU : ∀ i, ∀ b ∈ inBlockBonds (yb i) (nb i), frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i) :
    ‖gradL2 U Gf‖ ^ 2 ≤ ∑ i, (12 * δ i ^ 2 * (nb i : ℝ) ^ 3 + 12 * ((nb i : ℝ) * nb i)) * ‖c i‖ ^ 2 := by
  classical
  set B : ι → Finset (PeriodicLatticeSite L) := fun i => blockOf (yb i) (nb i) with hB
  -- pointwise
  set T1 : Bond L → ι → ℝ := fun b i => if b ∈ inBlockBonds (yb i) (nb i) then 4 * δ i ^ 2 * ‖c i‖ ^ 2 else 0
  set T2 : Bond L → ι → ℝ := fun b i =>
    if b.1 ∈ B i ∧ periodicLatticeShift b.1 b.2 ∉ B i then 2 * ‖c i‖ ^ 2 else 0
  set T3 : Bond L → ι → ℝ := fun b i =>
    if periodicLatticeShift b.1 b.2 ∈ B i ∧ b.1 ∉ B i then 2 * ‖c i‖ ^ 2 else 0
  have hT1 : ∀ b i, 0 ≤ T1 b i := fun b i => by simp only [T1]; split_ifs <;> positivity
  have hT2 : ∀ b i, 0 ≤ T2 b i := fun b i => by simp only [T2]; split_ifs <;> positivity
  have hT3 : ∀ b i, 0 ≤ T3 b i := fun b i => by simp only [T3]; split_ifs <;> positivity
  have hpt : ∀ b : Bond L, ‖gradL2 U Gf b‖ ^ 2 ≤ ∑ i, T1 b i + ∑ i, T2 b i + ∑ i, T3 b i := by
    intro b
    set h := periodicLatticeShift b.1 b.2
    by_cases hA : ∃ i, b.1 ∈ B i ∧ h ∈ B i
    · obtain ⟨i, ht, hh⟩ := hA
      have hbi : b ∈ inBlockBonds (yb i) (nb i) := mem_inBlockBonds.mpr ⟨ht, hh⟩
      have e : gradL2 U Gf b = RMap (U b) (c i) - c i := by
        rw [gradL2_apply', hon i h hh, hon i b.1 ht]
      have h1 : ‖gradL2 U Gf b‖ ≤ 2 * δ i * ‖c i‖ := by
        rw [e]
        refine (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) (c i)).trans ?_
        gcongr
        exact hU i b hbi
      have h2 : ‖gradL2 U Gf b‖ ^ 2 ≤ T1 b i := by
        simp only [T1, if_pos hbi]
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith
      have h3 : T1 b i ≤ ∑ i', T1 b i' := Finset.single_le_sum (fun i' _ => hT1 b i') (Finset.mem_univ i)
      have h4 : 0 ≤ ∑ i', T2 b i' := Finset.sum_nonneg (fun i' _ => hT2 b i')
      have h5 : 0 ≤ ∑ i', T3 b i' := Finset.sum_nonneg (fun i' _ => hT3 b i')
      linarith
    · push Not at hA
      have hbase : ‖gradL2 U Gf b‖ ^ 2 ≤ 2 * ‖Gf h‖ ^ 2 + 2 * ‖Gf b.1‖ ^ 2 := by
        rw [gradL2_apply']
        have h1 := norm_sub_le (RMap (U b) (Gf h)) (Gf b.1)
        rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h1
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg (‖Gf h‖ - ‖Gf b.1‖)]
      have htail : 2 * ‖Gf b.1‖ ^ 2 ≤ ∑ i, T2 b i := by
        by_cases ht : ∃ i, b.1 ∈ B i
        · obtain ⟨i, hi⟩ := ht
          have hh : h ∉ B i := hA i hi
          have e : 2 * ‖Gf b.1‖ ^ 2 = T2 b i := by
            rw [hon i b.1 hi]; simp only [T2]; exact (if_pos ⟨hi, hh⟩).symm
          rw [e]; exact Finset.single_le_sum (fun i' _ => hT2 b i') (Finset.mem_univ i)
        · push Not at ht
          rw [hoff b.1 ht]; simp only [norm_zero]
          have := Finset.sum_nonneg (fun i' (_ : i' ∈ Finset.univ) => hT2 b i'); nlinarith
      have hhead : 2 * ‖Gf h‖ ^ 2 ≤ ∑ i, T3 b i := by
        by_cases hh : ∃ i, h ∈ B i
        · obtain ⟨i, hi⟩ := hh
          have ht : b.1 ∉ B i := fun ht => hA i ht hi
          have e : 2 * ‖Gf h‖ ^ 2 = T3 b i := by
            rw [hon i h hi]; simp only [T3]; exact (if_pos ⟨hi, ht⟩).symm
          rw [e]; exact Finset.single_le_sum (fun i' _ => hT3 b i') (Finset.mem_univ i)
        · push Not at hh
          rw [hoff h hh]; simp only [norm_zero]
          have := Finset.sum_nonneg (fun i' (_ : i' ∈ Finset.univ) => hT3 b i'); nlinarith
      have h1 : 0 ≤ ∑ i', T1 b i' := Finset.sum_nonneg (fun i' _ => hT1 b i')
      linarith
  rw [PiLp.norm_sq_eq_of_L2]
  refine le_trans (Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpt b)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := T2),
    Finset.sum_comm (f := T3), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hc0 : 0 ≤ ‖c i‖ ^ 2 := sq_nonneg _
  have s1 : ∑ b, T1 b i ≤ 3 * (nb i : ℝ) ^ 3 * (4 * δ i ^ 2 * ‖c i‖ ^ 2) :=
    sum_inBlock_le (yb i) (nb i) _ (by positivity)
  have s2 : ∑ b, T2 b i ≤ 3 * ((nb i : ℝ) * nb i) * (2 * ‖c i‖ ^ 2) :=
    sum_out_le (yb i) (nb i) (hfit i) _ (by positivity)
  have s3 : ∑ b, T3 b i ≤ 3 * ((nb i : ℝ) * nb i) * (2 * ‖c i‖ ^ 2) :=
    sum_in_le (yb i) (nb i) _ (by positivity)
  nlinarith [s1, s2, s3]

#print axioms exit_top
#print axioms enter_bottom
#print axioms face_card
#print axioms card_out_le
#print axioms card_in_le
#print axioms card_inBlockBonds_le
#print axioms sum_out_le
#print axioms sum_in_le
#print axioms sum_inBlock_le
#print axioms grad_blockconst_le

#print axioms shift_apply_self
#print axioms shift_apply_ne
#print axioms face_card_gen

end AdalyFormal.M1Site
