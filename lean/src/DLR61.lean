import Mathlib

/-!
# DL61 -- the matrix exponential to second order at an ARBITRARY base point (explicit constants)

In the `ℓ^∞`-operator norm on `2×2` complex matrices (`Matrix.linftyOpNormedRing`, submultiplicative, `‖1‖ = 1`):
* `Dn A B n = Σ_{k<n} A^k B A^{n−1−k}`; `norm_Dn_le` : `‖Dn‖ ≤ n a^{n−1} b`;
  `norm_Rn_le` : `‖(A+B)^n − A^n − Dn‖ ≤ (a+b)^n − a^n − n a^{n−1} b` (exact scalar recursion);
* `expL A B = Σ_n (n!)⁻¹ Dn A B n` (the derivative of `exp` at `A` applied to `B`), linear in `B`;
* **`exp_second_order`** : `‖exp(A+B) − exp A − expL A B‖ ≤ ‖B‖² e^{‖A‖+‖B‖}`;
* `expL_sub_le` : `‖expL A B − B‖ ≤ (e^{‖A‖} − 1)‖B‖`;  `expL_le` : `‖expL A B‖ ≤ e^{‖A‖}‖B‖`.
No `fderiv` is used: everything is a statement about values (cf. the r8 notice on whole-torus jets).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer.ExpC11

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open Finset

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

noncomputable def Dn (A B : Mt) (n : ℕ) : Mt := ∑ k ∈ range n, A ^ k * B * A ^ (n - 1 - k)

theorem Dn_zero (A B : Mt) : Dn A B 0 = 0 := by simp [Dn]

theorem Dn_succ (A B : Mt) (n : ℕ) : Dn A B (n + 1) = A ^ n * B + Dn A B n * A := by
  unfold Dn
  rw [sum_range_succ, add_comm, Finset.sum_mul]
  congr 1
  · simp
  · refine sum_congr rfl (fun k hk => ?_)
    have hk' := mem_range.mp hk
    rw [show n + 1 - 1 - k = n - 1 - k + 1 by omega, pow_succ]
    noncomm_ring

theorem Dn_add (A B C : Mt) (n : ℕ) : Dn A (B + C) n = Dn A B n + Dn A C n := by
  unfold Dn; rw [← sum_add_distrib]; refine sum_congr rfl (fun k _ => ?_); noncomm_ring

theorem Dn_smul (A B : Mt) (c : ℝ) (n : ℕ) : Dn A (c • B) n = c • Dn A B n := by
  unfold Dn; rw [smul_sum]; refine sum_congr rfl (fun k _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc]

theorem hpow_mul (a : ℝ) (m : ℕ) : (m : ℝ) * a ^ (m - 1) * a = m * a ^ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega, pow_succ]; ring

theorem norm_Dn_le (A B : Mt) (n : ℕ) : ‖Dn A B n‖ ≤ n * ‖A‖ ^ (n - 1) * ‖B‖ := by
  induction n with
  | zero => simp [Dn_zero]
  | succ m ih =>
      rw [Dn_succ]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖A ^ m * B‖ ≤ ‖A‖ ^ m * ‖B‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le A m) (norm_nonneg _))
      have h2 : ‖Dn A B m * A‖ ≤ (m * ‖A‖ ^ (m - 1) * ‖B‖) * ‖A‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
      have h3 := hpow_mul ‖A‖ m
      have e : (m * ‖A‖ ^ (m - 1) * ‖B‖) * ‖A‖ = (m * ‖A‖ ^ (m - 1) * ‖A‖) * ‖B‖ := by ring
      rw [e, h3] at h2
      rw [show m + 1 - 1 = m by omega]
      push_cast
      nlinarith [h1, h2]

/-- the second-order remainder of the noncommutative binomial expansion -/
theorem norm_Rn_le (A B : Mt) (n : ℕ) :
    ‖(A + B) ^ n - A ^ n - Dn A B n‖ ≤ (‖A‖ + ‖B‖) ^ n - ‖A‖ ^ n - n * ‖A‖ ^ (n - 1) * ‖B‖ := by
  induction n with
  | zero => simp [Dn_zero]
  | succ m ih =>
      have e : (A + B) ^ (m + 1) - A ^ (m + 1) - Dn A B (m + 1)
          = Dn A B m * B + ((A + B) ^ m - A ^ m - Dn A B m) * (A + B) := by
        rw [Dn_succ, pow_succ, pow_succ]; noncomm_ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖Dn A B m * B‖ ≤ (m * ‖A‖ ^ (m - 1) * ‖B‖) * ‖B‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_Dn_le A B m) (norm_nonneg _))
      have h2 : ‖((A + B) ^ m - A ^ m - Dn A B m) * (A + B)‖
          ≤ ((‖A‖ + ‖B‖) ^ m - ‖A‖ ^ m - m * ‖A‖ ^ (m - 1) * ‖B‖) * (‖A‖ + ‖B‖) :=
        (norm_mul_le _ _).trans (mul_le_mul ih (norm_add_le _ _) (norm_nonneg _)
          (le_trans (norm_nonneg _) ih))
      have key : (m : ℝ) * ‖A‖ ^ (m - 1) * ‖B‖ * ‖B‖
          + ((‖A‖ + ‖B‖) ^ m - ‖A‖ ^ m - m * ‖A‖ ^ (m - 1) * ‖B‖) * (‖A‖ + ‖B‖)
          = (‖A‖ + ‖B‖) ^ (m + 1) - ‖A‖ ^ (m + 1) - ((m + 1 : ℕ) : ℝ) * ‖A‖ ^ (m + 1 - 1) * ‖B‖ := by
        have h3 := hpow_mul ‖A‖ m
        rw [show m + 1 - 1 = m by omega, pow_succ, pow_succ]
        push_cast
        have : (m : ℝ) * ‖A‖ ^ (m - 1) * ‖B‖ * ‖A‖ = m * ‖A‖ ^ m * ‖B‖ := by
          calc (m : ℝ) * ‖A‖ ^ (m - 1) * ‖B‖ * ‖A‖ = (m * ‖A‖ ^ (m - 1) * ‖A‖) * ‖B‖ := by ring
            _ = m * ‖A‖ ^ m * ‖B‖ := by rw [h3]
        nlinarith [this]
      linarith

/-! ## the series -/

theorem summable_shift_exp (a : ℝ) : Summable (fun n : ℕ => (n : ℝ) * a ^ (n - 1) / n.factorial) := by
  rw [← summable_nat_add_iff 1]
  refine (Real.summable_pow_div_factorial a).congr (fun n => ?_)
  rw [show n + 1 - 1 = n by omega, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem summable_Dn (A B : Mt) : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • Dn A B n) := by
  refine Summable.of_norm_bounded ((summable_shift_exp ‖A‖).mul_right ‖B‖) (fun n => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_Dn_le A B n
  have hf : (0 : ℝ) < n.factorial := by positivity
  calc ((n.factorial : ℝ)⁻¹) * ‖Dn A B n‖ ≤ ((n.factorial : ℝ)⁻¹) * (n * ‖A‖ ^ (n - 1) * ‖B‖) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (n : ℝ) * ‖A‖ ^ (n - 1) / n.factorial * ‖B‖ := by field_simp

/-- the derivative of `exp` at `A`, applied to `B` -/
noncomputable def expL (A B : Mt) : Mt := ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • Dn A B n

theorem expL_add (A B C : Mt) : expL A (B + C) = expL A B + expL A C := by
  unfold expL
  rw [← (summable_Dn A B).tsum_add (summable_Dn A C)]
  congr 1; funext n; rw [Dn_add, smul_add]

theorem expL_smul (A B : Mt) (c : ℝ) : expL A (c • B) = c • expL A B := by
  unfold expL
  have h := ((summable_Dn A B).hasSum).const_smul c
  rw [← h.tsum_eq]
  congr 1; funext n; rw [Dn_smul, smul_comm]

/-! ## the main bounds -/

theorem real_exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

/-- `Σ n a^{n−1}/n! = e^a` -/
theorem shift_exp_hasSum (a : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * a ^ (n - 1) / n.factorial) (Real.exp a) := by
  rw [← hasSum_nat_add_iff' 1]
  have h0 : ∑ i ∈ range 1, (fun n : ℕ => (n : ℝ) * a ^ (n - 1) / n.factorial) i = 0 := by simp
  rw [h0, sub_zero]
  refine (real_exp_hasSum a).congr_fun (fun n => ?_)
  show (((n + 1 : ℕ) : ℝ) * a ^ (n + 1 - 1) / ((n + 1).factorial : ℝ)) = a ^ n / n.factorial
  rw [show n + 1 - 1 = n by omega, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem mat_exp_hasSum (X : Mt) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • X ^ n) (NormedSpace.exp X) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X

/-- **the second-order expansion of `exp` at an arbitrary base point** (`‖B‖ ≤ 1`) -/
theorem exp_second_order (A B : Mt) (hB : ‖B‖ ≤ 1) :
    ‖NormedSpace.exp (A + B) - NormedSpace.exp A - expL A B‖ ≤ ‖B‖ ^ 2 * Real.exp ‖A‖ := by
  have h1 := mat_exp_hasSum (A + B)
  have h2 := mat_exp_hasSum A
  have h3 := (summable_Dn A B).hasSum
  have hS : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ((A + B) ^ n - A ^ n - Dn A B n))
      (NormedSpace.exp (A + B) - NormedSpace.exp A - expL A B) := by
    have := (h1.sub h2).sub h3
    refine this.congr_fun (fun n => ?_)
    simp only [smul_sub]
  set a := ‖A‖
  set b := ‖B‖
  have hg : HasSum (fun n : ℕ => ((a + b) ^ n / n.factorial - a ^ n / n.factorial
      - b * ((n : ℝ) * a ^ (n - 1) / n.factorial)))
      (Real.exp (a + b) - Real.exp a - b * Real.exp a) :=
    ((real_exp_hasSum (a + b)).sub (real_exp_hasSum a)).sub ((shift_exp_hasSum a).mul_left b)
  have hb := hS.norm_le_of_bounded hg (fun n => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := norm_Rn_le A B n
    have hf : (0 : ℝ) < n.factorial := by positivity
    calc ((n.factorial : ℝ)⁻¹) * ‖(A + B) ^ n - A ^ n - Dn A B n‖
        ≤ ((n.factorial : ℝ)⁻¹) * ((a + b) ^ n - a ^ n - n * a ^ (n - 1) * b) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (a + b) ^ n / n.factorial - a ^ n / n.factorial - b * ((n : ℝ) * a ^ (n - 1) / n.factorial) := by
          field_simp)
  refine hb.trans ?_
  have hb0 : 0 ≤ b := norm_nonneg _
  have hexp : Real.exp (a + b) - Real.exp a - b * Real.exp a = Real.exp a * (Real.exp b - 1 - b) := by
    rw [Real.exp_add]; ring
  rw [hexp]
  have h4 := Real.abs_exp_sub_one_sub_id_le (x := b) (by rw [abs_of_nonneg hb0]; exact hB)
  have h5 : Real.exp b - 1 - b ≤ b ^ 2 := le_trans (le_abs_self _) h4
  have := Real.exp_pos a
  nlinarith

theorem expL_le (A B : Mt) : ‖expL A B‖ ≤ Real.exp ‖A‖ * ‖B‖ := by
  have h3 := (summable_Dn A B).hasSum
  have hb := h3.norm_le_of_bounded ((shift_exp_hasSum ‖A‖).mul_right ‖B‖) (fun n => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := norm_Dn_le A B n
    calc ((n.factorial : ℝ)⁻¹) * ‖Dn A B n‖ ≤ ((n.factorial : ℝ)⁻¹) * (n * ‖A‖ ^ (n - 1) * ‖B‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (n : ℝ) * ‖A‖ ^ (n - 1) / n.factorial * ‖B‖ := by field_simp)
  exact hb

theorem Dn_one (A B : Mt) : Dn A B 1 = B := by simp [Dn]

theorem expL_sub_le (A B : Mt) : ‖expL A B - B‖ ≤ (Real.exp ‖A‖ - 1) * ‖B‖ := by
  have h3 := (summable_Dn A B).hasSum
  have hB : HasSum (fun n : ℕ => if n = 1 then B else 0) B := by
    convert hasSum_ite_eq 1 B using 1
  have hS := h3.sub hB
  have hg : HasSum (fun n : ℕ => (n : ℝ) * ‖A‖ ^ (n - 1) / n.factorial * ‖B‖ - (if n = 1 then ‖B‖ else 0))
      (Real.exp ‖A‖ * ‖B‖ - ‖B‖) := by
    have := ((shift_exp_hasSum ‖A‖).mul_right ‖B‖).sub (hasSum_ite_eq 1 ‖B‖)
    exact this
  have hb := hS.norm_le_of_bounded hg (fun n => by
    by_cases hn : n = 1
    · subst hn; simp [Dn_one]
    · rw [if_neg hn, if_neg hn, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := norm_Dn_le A B n
      calc ((n.factorial : ℝ)⁻¹) * ‖Dn A B n‖ ≤ ((n.factorial : ℝ)⁻¹) * (n * ‖A‖ ^ (n - 1) * ‖B‖) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (n : ℝ) * ‖A‖ ^ (n - 1) / n.factorial * ‖B‖ := by field_simp)
  refine hb.trans (le_of_eq ?_)
  ring

theorem expL_zero_base (B : Mt) : expL 0 B = B := by
  have h := expL_sub_le 0 B
  rw [norm_zero, Real.exp_zero, sub_self, zero_mul] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

#print axioms norm_Rn_le
#print axioms summable_Dn
#print axioms exp_second_order
#print axioms expL_le
#print axioms expL_sub_le
#print axioms expL_zero_base

end AdalyFormal.DLayer.ExpC11
