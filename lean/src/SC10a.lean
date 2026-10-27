import SC5a

/-!
# SC10a -- v2: the zero-mode estimates with a general sinc lower bound `σ`:
`SigmaOK z σ :≡ ∀ μ, σ |θ_μ| ≤ 2 |sin(θ_μ/2)|`.  `σ = 2/π` always holds; `σ = 15/16` holds when all `|θ_μ| ≤ 1`.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Sigma
variable {n : ℕ}

def SigmaOK (z : Fin 3 → Circle) (σ : ℝ) : Prop := ∀ μ, σ * |th z μ| ≤ 2 * |Real.sin (th z μ / 2)|

theorem sigmaOK_pi (z : Fin 3 → Circle) : SigmaOK z (2 / Real.pi) := by
  intro μ
  have hθ := th_mem z μ
  have habs : |th z μ / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  have h := abs_sin_ge (th z μ / 2) habs
  have e : |th z μ / 2| = |th z μ| / 2 := by rw [abs_div]; norm_num
  rw [e] at h
  have e2 : 2 / Real.pi * (|th z μ| / 2) = (2 / Real.pi * |th z μ|) / 2 := by ring
  rw [e2] at h
  linarith

theorem abs_sin_eq (y : ℝ) (h : |y| ≤ Real.pi) : |Real.sin y| = Real.sin |y| := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by
      rw [abs_of_nonneg h0] at h; exact h))]
  · have hy : 0 ≤ -y := by linarith
    have hy2 : -y ≤ Real.pi := by rw [abs_of_nonpos h0] at h; exact h
    rw [abs_of_nonpos h0, ← abs_neg (Real.sin y), ← Real.sin_neg,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy hy2)]

theorem sigmaOK_small (z : Fin 3 → Circle) (h : ∀ μ, |th z μ| ≤ 1) : SigmaOK z (15 / 16) := by
  intro μ
  have hθ := h μ
  by_cases h0 : th z μ = 0
  · rw [h0]; simp
  · have hpos : 0 < |th z μ| := abs_pos.mpr h0
    have hy : |th z μ / 2| = |th z μ| / 2 := by rw [abs_div]; norm_num
    have hpi := Real.pi_gt_three
    have e : |Real.sin (th z μ / 2)| = Real.sin (|th z μ| / 2) := by
      rw [abs_sin_eq (th z μ / 2) (by rw [hy]; linarith), hy]
    rw [e]
    have hc := Real.sin_gt_sub_cube (x := |th z μ| / 2) (by positivity) (by linarith)
    have h3 : |th z μ| ^ 3 ≤ |th z μ| := by
      have : |th z μ| ^ 3 = |th z μ| * |th z μ| ^ 2 := by ring
      rw [this]
      have h2 : |th z μ| ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith [hc, h3]

theorem Tm_lower_σ (hn : 0 < n) (z : Fin 3 → Circle) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : SigmaOK z σ) (μ : Fin 3) : σ * (n : ℝ) ≤ ‖Tm n z hn μ‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h1 : sg n z (k0 hn) μ = 1
  · unfold Tm
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    nlinarith
  · unfold Tm
    rw [geom_sum_eq h1, norm_div, sg_pow hn]
    have hz : ‖(z μ : ℂ) - 1‖ = ‖2 * Real.sin (th z μ / 2)‖ := by
      rw [z_eq_exp z μ]; exact Complex.norm_exp_I_mul_ofReal_sub_one _
    have hdiff : ‖sg n z (k0 hn) μ - 1‖ ≤ |th z μ| / n := by
      rw [sg0 hn]
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := th z μ / (n : ℝ))
      calc _ ≤ ‖th z μ / (n : ℝ)‖ := this
        _ = |th z μ| / n := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hnR]
    have hnorm_pos : 0 < ‖sg n z (k0 hn) μ - 1‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr h1
    rw [hz, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
    rw [le_div_iff₀ hnorm_pos]
    calc σ * (n : ℝ) * ‖sg n z (k0 hn) μ - 1‖
        ≤ σ * (n : ℝ) * (|th z μ| / n) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = σ * |th z μ| := by field_simp
      _ ≤ 2 * |Real.sin (th z μ / 2)| := hσ μ

theorem norm_prodT_σ (hn : 0 < n) (z : Fin 3 → Circle) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : SigmaOK z σ) : (σ * (n : ℝ)) ^ 3 ≤ ‖∏ μ, Tm n z hn μ‖ := by
  rw [norm_prod]
  have : (σ * (n : ℝ)) ^ 3 = ∏ _μ : Fin 3, (σ * (n : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this]
  exact Finset.prod_le_prod (fun _ _ => by positivity) (fun μ _ => Tm_lower_σ hn z σ hσ0 hσ1 hσ μ)

theorem Qm_e0_lower_σ (hn : 0 < n) (z : Fin 3 → Circle) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : SigmaOK z σ) (μ : Fin 3) :
    cn n * (σ * (n : ℝ)) ^ 4 ≤ ‖(cellSym hn z).Qm μ (pk n z (k0 hn))‖ := by
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have h : (cellSym hn z).Qm μ (pk n z (k0 hn)) = ((cn n : ℝ) : ℂ) * (Tm n z hn μ * ∏ ν, Tm n z hn ν) := by
    unfold pk
    rw [Qm_smul, Qm_pwv0 hn]
  rw [h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
  have h1 := Tm_lower_σ hn z σ hσ0 hσ1 hσ μ
  have h2 := norm_prodT_σ hn z σ hσ0 hσ1 hσ
  have h3 : (σ * (n : ℝ)) ^ 4 = (σ * (n : ℝ)) * (σ * (n : ℝ)) ^ 3 := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (norm_nonneg _)) hcn

theorem inner_e0_eps_lower_σ (hn : 0 < n) (z : Fin 3 → Circle) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : SigmaOK z σ) :
    (cn n) ^ 2 * (σ * (n : ℝ)) ^ 6 ≤ ‖⟪pk n z (k0 hn), epsV n⟫‖ ^ 2 := by
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have h : ⟪pk n z (k0 hn), epsV n⟫ = (starRingEnd ℂ) (((cn n : ℝ) : ℂ) * ∏ μ, Tm n z hn μ) := by
    rw [← inner_conj_symm, ← inner_eps_pwv0 hn]
    unfold pk
    rw [inner_smul_right, map_mul, Complex.conj_ofReal]
  rw [h, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
  have h2 := norm_prodT_σ hn z σ hσ0 hσ1 hσ
  have h3 : cn n * (σ * (n : ℝ)) ^ 3 ≤ cn n * ‖∏ μ, Tm n z hn μ‖ :=
    mul_le_mul_of_nonneg_left h2 hcn
  have h4 : (cn n * (σ * (n : ℝ)) ^ 3) ^ 2 ≤ (cn n * ‖∏ μ, Tm n z hn μ‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  calc (cn n) ^ 2 * (σ * (n : ℝ)) ^ 6 = (cn n * (σ * (n : ℝ)) ^ 3) ^ 2 := by ring
    _ ≤ _ := h4

theorem zeta_ge_σ (z : Fin 3 → Circle) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : SigmaOK z σ) :
    σ ^ 2 * Th2 z ≤ ∑ μ, ‖((z μ : Circle) : ℂ) - 1‖ ^ 2 := by
  unfold Th2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have hz : ‖((z μ : Circle) : ℂ) - 1‖ = ‖2 * Real.sin (th z μ / 2)‖ := by
    rw [z_eq_exp z μ]; exact Complex.norm_exp_I_mul_ofReal_sub_one _
  rw [hz, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have h3 := hσ μ
  have h4 : (σ * |th z μ|) ^ 2 ≤ (2 * |Real.sin (th z μ / 2)|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  calc σ ^ 2 * th z μ ^ 2 = (σ * |th z μ|) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ _ := h4

/-- a lower bound for the lowest Laplace eigenvalue: `n² λ₀ ≥ (4/π²) Θ²` -/
theorem lam0_ge (hn : 0 < n) (z : Fin 3 → Circle) :
    4 / Real.pi ^ 2 * Th2 z ≤ (n : ℝ) ^ 2 * lam n z (k0 hn) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold lam Th2
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  rw [sg0 hn, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hθ := th_mem z μ
  have habs : |th z μ / (n : ℝ) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_div, abs_of_pos hnR]
    have : |th z μ| ≤ Real.pi := by rw [abs_le]; exact ⟨by linarith [hθ.1], hθ.2⟩
    have h2 : |th z μ| / n ≤ Real.pi := by
      rw [div_le_iff₀ hnR]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have h1 := abs_sin_ge (th z μ / (n : ℝ) / 2) habs
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have e1 : |th z μ / (n : ℝ) / 2| = |th z μ| / n / 2 := by
    rw [abs_div, abs_div, abs_of_pos hnR]; norm_num
  rw [e1] at h1
  have h3 : 2 * (2 / Real.pi * (|th z μ| / n / 2)) ≤ 2 * |Real.sin (th z μ / (n : ℝ) / 2)| := by linarith
  have h4 : (2 * (2 / Real.pi * (|th z μ| / n / 2))) ^ 2 ≤ (2 * |Real.sin (th z μ / (n : ℝ) / 2)|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  calc 4 / Real.pi ^ 2 * th z μ ^ 2 = (n : ℝ) ^ 2 * (2 * (2 / Real.pi * (|th z μ| / n / 2))) ^ 2 := by
        field_simp
        rw [sq_abs]
        ring
    _ ≤ (n : ℝ) ^ 2 * (2 * |Real.sin (th z μ / (n : ℝ) / 2)|) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

end Sigma

#print axioms sigmaOK_pi
#print axioms sigmaOK_small
#print axioms Tm_lower_σ
#print axioms Qm_e0_lower_σ
#print axioms lam0_ge

end AdalyFormal.ScaledCoercivity
