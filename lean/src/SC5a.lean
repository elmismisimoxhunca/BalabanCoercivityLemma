import SC4e
import SC3f

/-!
# SC5a -- twist-angle estimates (`ζ² ≥ (4/π²) Θ²`, `λ0 ≤ Θ²/n²`, `λ0 > 0`) and the margin real lemma.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Angles
variable {n : ℕ}

/-- `Θ² = Σ θ_μ²` -/
noncomputable def Th2 (z : Fin 3 → Circle) : ℝ := ∑ μ, th z μ ^ 2

theorem Th2_le (z : Fin 3 → Circle) : Th2 z ≤ 3 * Real.pi ^ 2 := by
  unfold Th2
  have : ∀ μ : Fin 3, th z μ ^ 2 ≤ Real.pi ^ 2 := by
    intro μ
    have h := th_mem z μ
    have : |th z μ| ≤ Real.pi := by rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
    exact sq_le_sq.mpr (by rwa [abs_of_pos Real.pi_pos])
  calc ∑ μ, th z μ ^ 2 ≤ ∑ _μ : Fin 3, Real.pi ^ 2 := Finset.sum_le_sum (fun μ _ => this μ)
    _ = 3 * Real.pi ^ 2 := by simp

theorem zeta_ge (z : Fin 3 → Circle) :
    4 / Real.pi ^ 2 * Th2 z ≤ ∑ μ, ‖((z μ : Circle) : ℂ) - 1‖ ^ 2 := by
  unfold Th2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have hθ := th_mem z μ
  have habs : |th z μ / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  have h1 := abs_sin_ge (th z μ / 2) habs
  have hz : ‖((z μ : Circle) : ℂ) - 1‖ = ‖2 * Real.sin (th z μ / 2)‖ := by
    rw [z_eq_exp z μ]; exact Complex.norm_exp_I_mul_ofReal_sub_one _
  rw [hz, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have h2 : |th z μ| / Real.pi ≤ |Real.sin (th z μ / 2)| := by
    calc |th z μ| / Real.pi = 2 / Real.pi * (|th z μ| / 2) := by field_simp
      _ = 2 / Real.pi * |th z μ / 2| := by rw [abs_div]; norm_num
      _ ≤ _ := h1
  have h3 : 2 * (|th z μ| / Real.pi) ≤ 2 * |Real.sin (th z μ / 2)| := by linarith
  have h4 : (2 * (|th z μ| / Real.pi)) ^ 2 ≤ (2 * |Real.sin (th z μ / 2)|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  calc 4 / Real.pi ^ 2 * th z μ ^ 2 = (2 * (|th z μ| / Real.pi)) ^ 2 := by
        rw [mul_pow, div_pow, sq_abs]; ring
    _ ≤ _ := h4

theorem lam0_le (hn : 0 < n) (z : Fin 3 → Circle) : lam n z (k0 hn) ≤ Th2 z / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold lam Th2
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  rw [sg0 hn]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := th z μ / (n : ℝ))
  rw [Real.norm_eq_abs] at h
  have h2 : ‖Complex.exp (Complex.I * ((th z μ / (n : ℝ) : ℝ) : ℂ)) - 1‖ ^ 2 ≤ |th z μ / (n : ℝ)| ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  calc _ ≤ |th z μ / (n : ℝ)| ^ 2 := h2
    _ = th z μ ^ 2 / (n : ℝ) ^ 2 := by rw [sq_abs, div_pow]

theorem lam0_pos (hn : 0 < n) (z : Fin 3 → Circle) (μ0 : Fin 3) (hμ0 : ((z μ0 : Circle) : ℂ) ≠ 1) :
    0 < lam n z (k0 hn) := by
  have : sg n z (k0 hn) μ0 ≠ 1 := by
    intro h
    apply hμ0
    rw [← sg_pow hn z (k0 hn) μ0, h, one_pow]
  have h2 : 0 < ‖sg n z (k0 hn) μ0 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr this)
  unfold lam
  calc (0 : ℝ) < ‖sg n z (k0 hn) μ0 - 1‖ ^ 2 := by positivity
    _ ≤ _ := Finset.single_le_sum (f := fun ν => ‖sg n z (k0 hn) ν - 1‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ μ0)

end Angles

section RealLemmas

theorem mu_lower (a cA x X P Q : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ cA) (hx : 0 < x) (hxX : x ≤ X)
    (hP : cA * a / x ≤ P) (hQ : Q ≤ a / x + a / 4) (hQ0 : 0 ≤ Q) :
    cA * a / (X + a + a * X / 4) ≤ P / (1 + Q) := by
  have hX : 0 < X := lt_of_lt_of_le hx hxX
  have h1 : cA * a / x / (1 + a / x + a / 4) = cA * a / (x + a + a * x / 4) := by
    field_simp
  have hd1 : 0 < x + a + a * x / 4 := by positivity
  have hd2 : 0 < 1 + Q := by linarith
  calc cA * a / (X + a + a * X / 4) ≤ cA * a / (x + a + a * x / 4) := by
        apply div_le_div_of_nonneg_left (by positivity) hd1
        nlinarith
    _ = cA * a / x / (1 + a / x + a / 4) := h1.symm
    _ ≤ cA * a / x / (1 + Q) := by
        apply div_le_div_of_nonneg_left (by positivity) hd2
        linarith
    _ ≤ P / (1 + Q) := div_le_div_of_nonneg_right hP hd2.le

theorem ratio_mono {m0 m1 : ℝ} (h0 : 0 ≤ m0) (h : m0 ≤ m1) : m0 / (1 + m0) ≤ m1 / (1 + m1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end RealLemmas

#print axioms zeta_ge
#print axioms mu_lower

end AdalyFormal.ScaledCoercivity
