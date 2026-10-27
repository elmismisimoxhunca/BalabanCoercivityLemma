import FE1

/-!
# FE2 -- Schur test, the step bound on `Fin N`, and the 3-fold product difference (Mathlib only)
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.FlatExt

/-- **Schur test** for a finite kernel acting on vectors: majorant `M ≥ |K|` with row sums `≤ R`, column sums `≤ C`. -/
theorem schur {X Y V : Type*} [Fintype X] [Fintype Y] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (K M : X → Y → ℝ) (hKM : ∀ x y, |K x y| ≤ M x y) (R C : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ x, ∑ y, M x y ≤ R) (hC : ∀ y, ∑ x, M x y ≤ C) (w : Y → V) :
    ∑ x, ‖∑ y, K x y • w y‖ ^ 2 ≤ R * C * ∑ y, ‖w y‖ ^ 2 := by
  have hM0 : ∀ x y, 0 ≤ M x y := fun x y => (abs_nonneg _).trans (hKM x y)
  have hpt : ∀ x, ‖∑ y, K x y • w y‖ ^ 2 ≤ R * ∑ y, M x y * ‖w y‖ ^ 2 := by
    intro x
    have h1 : ‖∑ y, K x y • w y‖ ≤ ∑ y, M x y * ‖w y‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hKM x y) (norm_nonneg _)
    have h2 : (∑ y, M x y * ‖w y‖) ^ 2 ≤ (∑ y, M x y) * ∑ y, M x y * ‖w y‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => Real.sqrt (M x y))
        (fun y => Real.sqrt (M x y) * ‖w y‖)
      have e1 : ∀ y, Real.sqrt (M x y) * (Real.sqrt (M x y) * ‖w y‖) = M x y * ‖w y‖ := fun y => by
        rw [← mul_assoc, Real.mul_self_sqrt (hM0 x y)]
      have e2 : ∀ y, Real.sqrt (M x y) ^ 2 = M x y := fun y => Real.sq_sqrt (hM0 x y)
      have e3 : ∀ y, (Real.sqrt (M x y) * ‖w y‖) ^ 2 = M x y * ‖w y‖ ^ 2 := fun y => by
        rw [mul_pow, Real.sq_sqrt (hM0 x y)]
      simp only [e1, e2, e3] at this
      exact this
    have h4 : 0 ≤ ∑ y, M x y * ‖w y‖ ^ 2 :=
      Finset.sum_nonneg fun y _ => mul_nonneg (hM0 x y) (sq_nonneg _)
    calc ‖∑ y, K x y • w y‖ ^ 2 ≤ (∑ y, M x y * ‖w y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ y, M x y) * ∑ y, M x y * ‖w y‖ ^ 2 := h2
      _ ≤ R * ∑ y, M x y * ‖w y‖ ^ 2 := mul_le_mul_of_nonneg_right (hR x) h4
  calc ∑ x, ‖∑ y, K x y • w y‖ ^ 2 ≤ ∑ x, R * ∑ y, M x y * ‖w y‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = R * ∑ y, (∑ x, M x y) * ‖w y‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
    _ ≤ R * ∑ y, C * ‖w y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right (hC y) (sq_nonneg _)) hR0
    _ = R * C * ∑ y, ‖w y‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

theorem pos_of_neZero_eq_mul {N Nu n : ℕ} [NeZero N] (hN : N = Nu * n) : 0 < Nu := by
  rcases Nat.eq_zero_or_pos Nu with h | h
  · have := NeZero.ne N
    rw [hN, h, zero_mul] at this
    exact absurd rfl this
  · exact h

/-- the step bound in cyclic coordinates: `x ↦ x + 1` on `Fin N`. -/
theorem abs_phi_step_fin (Nu n : ℕ) (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = Nu * n) (a b : Fin N) :
    |phi n Nu (a + 1 - b).val - phi n Nu (a - b).val| ≤ 6 / n * chi n Nu (a - b).val := by
  have hNu : 0 < Nu := pos_of_neZero_eq_mul hN
  have he : a + 1 - b = (a - b) + 1 := by abel
  have hv : (a + 1 - b).val = ((a - b).val + 1) % N := by
    rw [he, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hv' : ((a - b).val + 1) % N = ((a - b).val + 1) % (Nu * n) :=
    congrArg (fun m => ((a - b).val + 1) % m) hN
  rw [hv, hv']
  have hlt : (a - b).val < Nu * n := by have := (a - b).isLt; omega
  exact abs_phi_step n Nu _ hn hNu hlt

/-- one factor of a 3-fold product changed. -/
theorem abs_prod3_update_sub (F G B : Fin 3 → ℝ) (μ : Fin 3) (c : ℝ) (hc : 0 ≤ c)
    (hG : ∀ ν, ν ≠ μ → G ν = F ν) (hF : ∀ ν, |F ν| ≤ B ν) (hD : |G μ - F μ| ≤ c * B μ) :
    |∏ ν, G ν - ∏ ν, F ν| ≤ c * ∏ ν, B ν := by
  have hB : ∀ ν, 0 ≤ B ν := fun ν => (abs_nonneg _).trans (hF ν)
  rw [Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three]
  have hμ : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases hμ with rfl | rfl | rfl
  · rw [hG 1 (by decide), hG 2 (by decide)]
    have : G 0 * F 1 * F 2 - F 0 * F 1 * F 2 = (G 0 - F 0) * F 1 * F 2 := by ring
    rw [this, abs_mul, abs_mul]
    calc |G 0 - F 0| * |F 1| * |F 2| ≤ (c * B 0) * B 1 * B 2 :=
          mul_le_mul (mul_le_mul hD (hF 1) (abs_nonneg _) (mul_nonneg hc (hB 0))) (hF 2) (abs_nonneg _)
            (mul_nonneg (mul_nonneg hc (hB 0)) (hB 1))
      _ = c * (B 0 * B 1 * B 2) := by ring
  · rw [hG 0 (by decide), hG 2 (by decide)]
    have : F 0 * G 1 * F 2 - F 0 * F 1 * F 2 = F 0 * (G 1 - F 1) * F 2 := by ring
    rw [this, abs_mul, abs_mul]
    calc |F 0| * |G 1 - F 1| * |F 2| ≤ B 0 * (c * B 1) * B 2 :=
          mul_le_mul (mul_le_mul (hF 0) hD (abs_nonneg _) (hB 0)) (hF 2) (abs_nonneg _)
            (mul_nonneg (hB 0) (mul_nonneg hc (hB 1)))
      _ = c * (B 0 * B 1 * B 2) := by ring
  · rw [hG 0 (by decide), hG 1 (by decide)]
    have : F 0 * F 1 * G 2 - F 0 * F 1 * F 2 = F 0 * F 1 * (G 2 - F 2) := by ring
    rw [this, abs_mul, abs_mul]
    calc |F 0| * |F 1| * |G 2 - F 2| ≤ B 0 * B 1 * (c * B 2) :=
          mul_le_mul (mul_le_mul (hF 0) (hF 1) (abs_nonneg _) (hB 0)) hD (abs_nonneg _)
            (mul_nonneg (hB 0) (hB 1))
      _ = c * (B 0 * B 1 * B 2) := by ring

/-- `|∏ F| ≤ ∏ B` from `|F ν| ≤ B ν`. -/
theorem abs_prod_le_prod {ι : Type*} [Fintype ι] (F B : ι → ℝ) (hF : ∀ ν, |F ν| ≤ B ν) :
    |∏ ν, F ν| ≤ ∏ ν, B ν := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun ν _ => abs_nonneg _) (fun ν _ => hF ν)

#print axioms schur
#print axioms abs_phi_step_fin
#print axioms abs_prod3_update_sub
#print axioms abs_prod_le_prod

end AdalyFormal.FlatExt
