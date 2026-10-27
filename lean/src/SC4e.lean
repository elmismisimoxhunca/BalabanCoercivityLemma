import SC4d

/-!
# SC4e -- the zero-mode data: `T_μ = Σ_{i<n} σ_μ^i`, `⟨ε, e_0⟩ = c_n Π T_μ`, `Qm_μ e_0 = T_μ ⟨ε,e_0⟩`, and the
explicit lower bounds `‖T_μ‖ ≥ 2n/π`.   Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Zero
variable {n : ℕ}

/-- `T_μ = Σ_{i<n} σ_{0,μ}^i` -/
noncomputable def Tm (n : ℕ) (z : Fin 3 → Circle) (hn : 0 < n) (μ : Fin 3) : ℂ :=
  ∑ i ∈ Finset.range n, (sg n z (k0 hn) μ) ^ i

theorem sg0 (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) :
    sg n z (k0 hn) μ = Complex.exp (Complex.I * (((th z μ) / (n : ℝ) : ℝ) : ℂ)) := by
  unfold sg k0
  simp

theorem abs_sin_ge (y : ℝ) (h : |y| ≤ Real.pi / 2) : 2 / Real.pi * |y| ≤ |Real.sin y| := by
  rcases le_total 0 y with h0 | h0
  · have h1 := Real.mul_le_sin h0 (by rwa [abs_of_nonneg h0] at h)
    rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by
      have := Real.pi_pos; rw [abs_of_nonneg h0] at h; linarith))]
    exact h1
  · have h1 := Real.mul_le_sin (neg_nonneg.mpr h0) (by rwa [abs_of_nonpos h0] at h)
    rw [Real.sin_neg] at h1
    rw [abs_of_nonpos h0]
    exact h1.trans (neg_le_abs _)

theorem Tm_lower (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) :
    2 * (n : ℝ) / Real.pi ≤ ‖Tm n z hn μ‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hpi2 : 2 ≤ Real.pi := by linarith [Real.pi_gt_three]
  by_cases h1 : sg n z (k0 hn) μ = 1
  · unfold Tm
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast, div_le_iff₀ hpi]
    nlinarith
  · unfold Tm
    rw [geom_sum_eq h1, norm_div, sg_pow hn]
    have hθ := th_mem z μ
    have hz : ‖(z μ : ℂ) - 1‖ = ‖2 * Real.sin (th z μ / 2)‖ := by
      rw [z_eq_exp z μ]; exact Complex.norm_exp_I_mul_ofReal_sub_one _
    have hs : |th z μ| / Real.pi ≤ |Real.sin (th z μ / 2)| := by
      have habs : |th z μ / 2| ≤ Real.pi / 2 := by
        rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
      have := abs_sin_ge (th z μ / 2) habs
      calc |th z μ| / Real.pi = 2 / Real.pi * (|th z μ| / 2) := by field_simp
        _ = 2 / Real.pi * |th z μ / 2| := by rw [abs_div]; norm_num
        _ ≤ _ := this
    have hdiff : ‖sg n z (k0 hn) μ - 1‖ ≤ |th z μ| / n := by
      rw [sg0 hn]
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := th z μ / (n : ℝ))
      calc _ ≤ ‖th z μ / (n : ℝ)‖ := this
        _ = |th z μ| / n := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hnR]
    have hθne : th z μ ≠ 0 := by
      intro h0
      apply h1
      rw [sg0 hn, h0]; simp
    have hθpos : 0 < |th z μ| := abs_pos.mpr hθne
    have hnorm_pos : 0 < ‖sg n z (k0 hn) μ - 1‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr h1
    rw [hz, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
    rw [le_div_iff₀ hnorm_pos]
    calc 2 * (n : ℝ) / Real.pi * ‖sg n z (k0 hn) μ - 1‖
        ≤ 2 * (n : ℝ) / Real.pi * (|th z μ| / n) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 2 * (|th z μ| / Real.pi) := by field_simp
      _ ≤ 2 * |Real.sin (th z μ / 2)| := by linarith

theorem inner_eps_pwv0 (hn : 0 < n) (z : Fin 3 → Circle) :
    ⟪epsV n, pwv n z (k0 hn)⟫ = ∏ μ, Tm n z hn μ := by
  classical
  rw [PiLp.inner_apply]
  simp only [epsV, pwv, pw, cc, zpow_natCast]
  simp only [RCLike.inner_apply, map_one, mul_one]
  have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
    (fun μ s => (sg n z (k0 hn) μ) ^ (s : ℕ))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl (fun μ _ => ?_)
  unfold Tm
  rw [Fin.sum_univ_eq_sum_range (fun i => (sg n z (k0 hn) μ) ^ i) n]

theorem iter_pwv0 (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (i : ℕ) :
    (Su hn z μ)^[i] (pwv n z (k0 hn)) = (sg n z (k0 hn) μ) ^ i • pwv n z (k0 hn) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, Su_pwv hn, smul_smul, pow_succ]

theorem Qm_pwv0 (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) :
    (cellSym hn z).Qm μ (pwv n z (k0 hn)) = Tm n z hn μ * ∏ ν, Tm n z hn ν := by
  show ⟪epsV n, ∑ i ∈ Finset.range n, (Su hn z μ)^[i] (pwv n z (k0 hn))⟫ = _
  simp only [iter_pwv0 hn]
  rw [← Finset.sum_smul, inner_smul_right, inner_eps_pwv0 hn]
  rfl

theorem norm_epsV_sq (hn : 0 < n) : ‖epsV n‖ ^ 2 = (n : ℝ) ^ 3 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [epsV, card_cell]

theorem norm_prodT (hn : 0 < n) (z : Fin 3 → Circle) :
    (2 * (n : ℝ) / Real.pi) ^ 3 ≤ ‖∏ μ, Tm n z hn μ‖ := by
  rw [norm_prod]
  have : (2 * (n : ℝ) / Real.pi) ^ 3 = ∏ _μ : Fin 3, (2 * (n : ℝ) / Real.pi) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this]
  exact Finset.prod_le_prod (fun _ _ => by positivity) (fun μ _ => Tm_lower hn z μ)

theorem Qm_e0_lower (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) :
    cn n * (2 * (n : ℝ) / Real.pi) ^ 4 ≤ ‖(cellSym hn z).Qm μ (pk n z (k0 hn))‖ := by
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have h : (cellSym hn z).Qm μ (pk n z (k0 hn)) = ((cn n : ℝ) : ℂ) * (Tm n z hn μ * ∏ ν, Tm n z hn ν) := by
    unfold pk
    rw [Qm_smul, Qm_pwv0 hn]
  rw [h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
  have h1 := Tm_lower hn z μ
  have h2 := norm_prodT hn z
  have h3 : (2 * (n : ℝ) / Real.pi) ^ 4 = (2 * (n : ℝ) / Real.pi) * (2 * (n : ℝ) / Real.pi) ^ 3 := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (norm_nonneg _)) hcn

theorem inner_e0_eps_lower (hn : 0 < n) (z : Fin 3 → Circle) :
    (cn n) ^ 2 * (2 * (n : ℝ) / Real.pi) ^ 6 ≤ ‖⟪pk n z (k0 hn), epsV n⟫‖ ^ 2 := by
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have h : ⟪pk n z (k0 hn), epsV n⟫ = (starRingEnd ℂ) (((cn n : ℝ) : ℂ) * ∏ μ, Tm n z hn μ) := by
    rw [← inner_conj_symm, ← inner_eps_pwv0 hn]
    unfold pk
    rw [inner_smul_right, map_mul, Complex.conj_ofReal]
  rw [h, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcn]
  have h2 := norm_prodT hn z
  have h3 : cn n * (2 * (n : ℝ) / Real.pi) ^ 3 ≤ cn n * ‖∏ μ, Tm n z hn μ‖ :=
    mul_le_mul_of_nonneg_left h2 hcn
  have h4 : (cn n * (2 * (n : ℝ) / Real.pi) ^ 3) ^ 2 ≤ (cn n * ‖∏ μ, Tm n z hn μ‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  calc (cn n) ^ 2 * (2 * (n : ℝ) / Real.pi) ^ 6 = (cn n * (2 * (n : ℝ) / Real.pi) ^ 3) ^ 2 := by ring
    _ ≤ _ := h4

end Zero

#print axioms Tm_lower
#print axioms Qm_e0_lower
#print axioms inner_e0_eps_lower

end AdalyFormal.ScaledCoercivity
