import MI24

/-!
# MI25 -- the tent profile: pointwise step/edge bounds and the gradient energy of a tent field (M1 lane E, 2026-10-13)

`φ = phiB n y` (MI24, mean one on `B(y,n)`, `0 ≤ φ ≤ 4`).
* `phiB_coef` : `n³/S_n³ · n · ((n+1)²/4)² ≤ 14/n`;
* `phiB_step` : `|φ(x+μ) − φ(x)| ≤ 14/n` when both ends lie in the block;
* `phiB_out` / `phiB_in` : `φ ≤ 14/n` at a block site whose `μ`-neighbour leaves (enters) the block;
* **`grad_tent_le`** : for `G = Σ_i φ_i c_i` on pairwise disjoint fitting blocks (`0` elsewhere), profiles bounded by `Φ_i`,
  in-block steps `≤ s_i`, edge values `≤ e_i`, in-block links `‖U_b − 1‖_F ≤ δ_i`:
  `‖D_U G‖² ≤ Σ_i (3 n_i³ (8 Φ_i² δ_i² + 2 s_i²) + 12 n_i² e_i²) ‖c_i‖²` (same bond bookkeeping as lane C's `grad_blockconst_le`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.M1Site
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open Finset

variable {L : PeriodicLatticeExtent}

/-- the profile constant against `14/n`. -/
theorem phiB_coef (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ 3 / Sn n ^ 3 * ((n : ℝ) * (((n : ℝ) + 1) ^ 2 / 4) ^ 2) ≤ 14 / n := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : (n : ℝ) ^ 3 / Sn n ^ 3 * ((n : ℝ) * (((n : ℝ) + 1) ^ 2 / 4) ^ 2)
      = 27 * (n : ℝ) * ((n : ℝ) + 1) / (2 * ((n : ℝ) + 2) ^ 3) := by
    unfold Sn; field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((n : ℝ)), mul_pos (show (0:ℝ) < n by linarith) (show (0:ℝ) < n by linarith)]

theorem tp_nonneg_of {n t : ℕ} (ht : t < n) : 0 ≤ tp n t := (tp_pos ht).le

/-- the off-axis product of a block site. -/
theorem erase_prod_bounds {n : ℕ} {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y n) (μ : Fin 3) :
    0 ≤ ∏ ν ∈ univ.erase μ, tp n ((x ν).val - (y ν).val)
      ∧ ∏ ν ∈ univ.erase μ, tp n ((x ν).val - (y ν).val) ≤ (((n : ℝ) + 1) ^ 2 / 4) ^ 2 := by
  rw [mem_blockOf] at hx
  have h0 : ∀ ν, 0 ≤ tp n ((x ν).val - (y ν).val) := fun ν => tp_nonneg_of (by have := hx ν; omega)
  refine ⟨prod_nonneg (fun ν _ => h0 ν), ?_⟩
  have h1 : ∏ ν ∈ univ.erase μ, tp n ((x ν).val - (y ν).val) ≤ ∏ ν ∈ univ.erase μ, (((n : ℝ) + 1) ^ 2 / 4) :=
    prod_le_prod (fun ν _ => h0 ν) (fun ν _ => tp_le)
  rw [prod_const, card_erase_of_mem (mem_univ μ), card_univ, Fintype.card_fin] at h1
  exact h1

theorem phiB_split (n : ℕ) {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y n) (μ : Fin 3) :
    phiB n y x = (n : ℝ) ^ 3 / Sn n ^ 3 * (tp n ((x μ).val - (y μ).val) * ∏ ν ∈ univ.erase μ, tp n ((x ν).val - (y ν).val)) := by
  classical
  unfold phiB
  rw [if_pos hx, ← mul_prod_erase univ (fun ν => tp n ((x ν).val - (y ν).val)) (mem_univ μ)]

/-- an edge value of the tent: `tp = n` on the `μ`-axis. -/
theorem phiB_edge_val (n : ℕ) (hn : 1 ≤ n) {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y n) (μ : Fin 3)
    (ht : tp n ((x μ).val - (y μ).val) = n) : phiB n y x ≤ 14 / n := by
  rw [phiB_split n hx μ, ht]
  have hb := erase_prod_bounds hx μ
  have hS := Sn_pos hn
  have hc : (0 : ℝ) ≤ (n : ℝ) ^ 3 / Sn n ^ 3 := by positivity
  refine le_trans ?_ (phiB_coef n hn)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg _)) hc

theorem phiB_out (n : ℕ) (hn : 1 ≤ n) {y x : PeriodicLatticeSite L} (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)
    (hx : x ∈ blockOf y n) (μ : Fin 3) (hout : periodicLatticeShift x μ ∉ blockOf y n) : phiB n y x ≤ 14 / n := by
  have h := exit_top hfit hx μ hout
  refine phiB_edge_val n hn hx μ ?_
  have : (x μ).val - (y μ).val = n - 1 := by omega
  rw [this, tp_last hn]

theorem phiB_in (n : ℕ) (hn : 1 ≤ n) {y x : PeriodicLatticeSite L} (μ : Fin 3)
    (hin : periodicLatticeShift x μ ∈ blockOf y n) (hx : x ∉ blockOf y n) :
    phiB n y (periodicLatticeShift x μ) ≤ 14 / n := by
  have h := enter_bottom hin hx
  refine phiB_edge_val n hn hin μ ?_
  rw [h, Nat.sub_self, tp_zero]

theorem phiB_step (n : ℕ) (hn : 1 ≤ n) {y x : PeriodicLatticeSite L} (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1)
    (hx : x ∈ blockOf y n) (μ : Fin 3) (hh : periodicLatticeShift x μ ∈ blockOf y n) :
    |phiB n y (periodicLatticeShift x μ) - phiB n y x| ≤ 14 / n := by
  rw [phiB_split n hh μ, phiB_split n hx μ]
  have hpe : ∏ ν ∈ univ.erase μ, tp n (((periodicLatticeShift x μ) ν).val - (y ν).val)
      = ∏ ν ∈ univ.erase μ, tp n ((x ν).val - (y ν).val) := by
    refine prod_congr rfl (fun ν hν => ?_)
    rw [shift_apply_ne x (ne_of_mem_erase hν)]
  rw [hpe]
  have hb := erase_prod_bounds hx μ
  have hS := Sn_pos hn
  have hc : (0 : ℝ) ≤ (n : ℝ) ^ 3 / Sn n ^ 3 := by positivity
  have hstep : |tp n (((periodicLatticeShift x μ) μ).val - (y μ).val) - tp n ((x μ).val - (y μ).val)| ≤ n := by
    have hxm := (mem_blockOf.mp hx) μ
    have hhm := (mem_blockOf.mp hh) μ
    have hsa := shift_apply_self x μ
    have hf := hfit μ
    by_cases hl : x μ = Fin.last (L μ)
    · rw [if_pos hl] at hsa
      have hxl : (x μ).val = L μ := by rw [hl, Fin.val_last]
      have e1 : ((periodicLatticeShift x μ) μ).val - (y μ).val = 0 := by omega
      have e2 : (x μ).val - (y μ).val = n - 1 := by omega
      rw [e1, e2, tp_zero, tp_last hn, sub_self, abs_zero]
      exact Nat.cast_nonneg _
    · rw [if_neg hl] at hsa
      have e1 : ((periodicLatticeShift x μ) μ).val - (y μ).val = ((x μ).val - (y μ).val) + 1 := by omega
      rw [e1]
      exact tp_step (by omega)
  rw [← mul_sub, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hb.1]
  refine le_trans ?_ (phiB_coef n hn)
  exact mul_le_mul_of_nonneg_left (mul_le_mul hstep hb.2 hb.1 (Nat.cast_nonneg _)) hc

/-- **gradient energy of a tent field**. -/
theorem grad_tent_le {ι : Type*} [Fintype ι] (U : Cfg L) (yb : ι → PeriodicLatticeSite L) (nb : ι → ℕ)
    (hfit : ∀ i, ∀ μ, (yb i μ).val + nb i ≤ L μ + 1)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (blockOf (yb i) (nb i)) (blockOf (yb i') (nb i')))
    (c : ι → SuTwo) (φ : ι → PeriodicLatticeSite L → ℝ) (Gf : SiteL2 L)
    (hon : ∀ i, ∀ x ∈ blockOf (yb i) (nb i), Gf x = φ i x • c i)
    (hoff : ∀ x, (∀ i, x ∉ blockOf (yb i) (nb i)) → Gf x = 0)
    (Φ s e : ι → ℝ) (hφ0 : ∀ i x, 0 ≤ φ i x) (hφΦ : ∀ i x, φ i x ≤ Φ i)
    (hstep : ∀ i, ∀ b ∈ inBlockBonds (yb i) (nb i), |φ i (periodicLatticeShift b.1 b.2) - φ i b.1| ≤ s i)
    (hout : ∀ i x (μ : Fin 3), x ∈ blockOf (yb i) (nb i) → periodicLatticeShift x μ ∉ blockOf (yb i) (nb i) → φ i x ≤ e i)
    (hin : ∀ i x (μ : Fin 3), periodicLatticeShift x μ ∈ blockOf (yb i) (nb i) → x ∉ blockOf (yb i) (nb i) →
      φ i (periodicLatticeShift x μ) ≤ e i)
    (δ : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hU : ∀ i, ∀ b ∈ inBlockBonds (yb i) (nb i), frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i) :
    ‖gradL2 U Gf‖ ^ 2 ≤ ∑ i, (3 * (nb i : ℝ) ^ 3 * (8 * Φ i ^ 2 * δ i ^ 2 + 2 * s i ^ 2)
      + 12 * ((nb i : ℝ) * nb i) * e i ^ 2) * ‖c i‖ ^ 2 := by
  classical
  set B : ι → Finset (PeriodicLatticeSite L) := fun i => blockOf (yb i) (nb i) with hB
  have hΦ0 : ∀ i, 0 ≤ Φ i := fun i => (hφ0 i (yb i)).trans (hφΦ i (yb i))
  set T1 : Bond L → ι → ℝ := fun b i =>
    if b ∈ inBlockBonds (yb i) (nb i) then (8 * Φ i ^ 2 * δ i ^ 2 + 2 * s i ^ 2) * ‖c i‖ ^ 2 else 0
  set T2 : Bond L → ι → ℝ := fun b i =>
    if b.1 ∈ B i ∧ periodicLatticeShift b.1 b.2 ∉ B i then 2 * e i ^ 2 * ‖c i‖ ^ 2 else 0
  set T3 : Bond L → ι → ℝ := fun b i =>
    if periodicLatticeShift b.1 b.2 ∈ B i ∧ b.1 ∉ B i then 2 * e i ^ 2 * ‖c i‖ ^ 2 else 0
  have hT1 : ∀ b i, 0 ≤ T1 b i := fun b i => by simp only [T1]; split_ifs <;> positivity
  have hT2 : ∀ b i, 0 ≤ T2 b i := fun b i => by simp only [T2]; split_ifs <;> positivity
  have hT3 : ∀ b i, 0 ≤ T3 b i := fun b i => by simp only [T3]; split_ifs <;> positivity
  have hpt : ∀ b : Bond L, ‖gradL2 U Gf b‖ ^ 2 ≤ ∑ i, T1 b i + ∑ i, T2 b i + ∑ i, T3 b i := by
    intro b
    set h := periodicLatticeShift b.1 b.2
    by_cases hA : ∃ i, b.1 ∈ B i ∧ h ∈ B i
    · obtain ⟨i, ht, hh⟩ := hA
      have hbi : b ∈ inBlockBonds (yb i) (nb i) := mem_inBlockBonds.mpr ⟨ht, hh⟩
      have e : gradL2 U Gf b = φ i h • (RMap (U b) (c i) - c i) + (φ i h - φ i b.1) • c i := by
        rw [gradL2_apply', hon i h hh, hon i b.1 ht, map_smul, smul_sub, sub_smul]; abel
      have h1 : ‖gradL2 U Gf b‖ ≤ Φ i * (2 * δ i * ‖c i‖) + s i * ‖c i‖ := by
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 i h)]
          refine mul_le_mul (hφΦ i h) ?_ (norm_nonneg _) (hΦ0 i)
          refine (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) (c i)).trans ?_
          gcongr
          exact hU i b hbi
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hstep i b hbi) (norm_nonneg _)
      have h2 : ‖gradL2 U Gf b‖ ^ 2 ≤ T1 b i := by
        simp only [T1, if_pos hbi]
        have hn0 := norm_nonneg (gradL2 U Gf b)
        have hc0 := norm_nonneg (c i)
        have hs0 : 0 ≤ s i := (abs_nonneg _).trans (hstep i b hbi)
        have hsq := pow_le_pow_left₀ hn0 h1 2
        nlinarith [sq_nonneg (Φ i * (2 * δ i * ‖c i‖) - s i * ‖c i‖)]
      have h3 : T1 b i ≤ ∑ i', T1 b i' := single_le_sum (fun i' _ => hT1 b i') (mem_univ i)
      have h4 : 0 ≤ ∑ i', T2 b i' := sum_nonneg (fun i' _ => hT2 b i')
      have h5 : 0 ≤ ∑ i', T3 b i' := sum_nonneg (fun i' _ => hT3 b i')
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
          have hv : ‖Gf b.1‖ ≤ e i * ‖c i‖ := by
            rw [hon i b.1 hi, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 i b.1)]
            exact mul_le_mul_of_nonneg_right (hout i b.1 b.2 hi hh) (norm_nonneg _)
          have e' : T2 b i = 2 * e i ^ 2 * ‖c i‖ ^ 2 := by simp only [T2]; exact if_pos ⟨hi, hh⟩
          have hsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
          rw [mul_pow] at hsq
          have := single_le_sum (fun i' _ => hT2 b i') (mem_univ i)
          rw [e'] at this
          nlinarith
        · push Not at ht
          rw [hoff b.1 ht]; simp only [norm_zero]
          have := sum_nonneg (fun i' (_ : i' ∈ univ) => hT2 b i'); nlinarith
      have hhead : 2 * ‖Gf h‖ ^ 2 ≤ ∑ i, T3 b i := by
        by_cases hh : ∃ i, h ∈ B i
        · obtain ⟨i, hi⟩ := hh
          have ht : b.1 ∉ B i := fun ht => hA i ht hi
          have hv : ‖Gf h‖ ≤ e i * ‖c i‖ := by
            rw [hon i h hi, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 i h)]
            exact mul_le_mul_of_nonneg_right (hin i b.1 b.2 hi ht) (norm_nonneg _)
          have e' : T3 b i = 2 * e i ^ 2 * ‖c i‖ ^ 2 := by simp only [T3]; exact if_pos ⟨hi, ht⟩
          have hsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
          rw [mul_pow] at hsq
          have := single_le_sum (fun i' _ => hT3 b i') (mem_univ i)
          rw [e'] at this
          nlinarith
        · push Not at hh
          rw [hoff h hh]; simp only [norm_zero]
          have := sum_nonneg (fun i' (_ : i' ∈ univ) => hT3 b i'); nlinarith
      have h1 : 0 ≤ ∑ i', T1 b i' := sum_nonneg (fun i' _ => hT1 b i')
      linarith
  rw [PiLp.norm_sq_eq_of_L2]
  refine le_trans (sum_le_sum (fun b (_ : b ∈ univ) => hpt b)) ?_
  rw [sum_add_distrib, sum_add_distrib, sum_comm, sum_comm (f := T2),
    sum_comm (f := T3), ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum (fun i _ => ?_)
  have hc0 : 0 ≤ ‖c i‖ ^ 2 := sq_nonneg _
  have s1 : ∑ b, T1 b i ≤ 3 * (nb i : ℝ) ^ 3 * ((8 * Φ i ^ 2 * δ i ^ 2 + 2 * s i ^ 2) * ‖c i‖ ^ 2) :=
    sum_inBlock_le (yb i) (nb i) _ (by positivity)
  have s2 : ∑ b, T2 b i ≤ 3 * ((nb i : ℝ) * nb i) * (2 * e i ^ 2 * ‖c i‖ ^ 2) :=
    sum_out_le (yb i) (nb i) (hfit i) _ (by positivity)
  have s3 : ∑ b, T3 b i ≤ 3 * ((nb i : ℝ) * nb i) * (2 * e i ^ 2 * ‖c i‖ ^ 2) :=
    sum_in_le (yb i) (nb i) _ (by positivity)
  nlinarith [s1, s2, s3]

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.phiB_coef
#print axioms AdalyFormal.M1IMS.erase_prod_bounds
#print axioms AdalyFormal.M1IMS.phiB_split
#print axioms AdalyFormal.M1IMS.phiB_edge_val
#print axioms AdalyFormal.M1IMS.phiB_out
#print axioms AdalyFormal.M1IMS.phiB_in
#print axioms AdalyFormal.M1IMS.phiB_step
#print axioms AdalyFormal.M1IMS.grad_tent_le
#print axioms AdalyFormal.M1IMS.tp_nonneg_of
