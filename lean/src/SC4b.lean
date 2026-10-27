import SC4a

/-!
# SC4b -- orthogonality of the plane waves and the orthonormal basis of the cell.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Orth
variable {n : ℕ}

theorem sg_inj (hn : 0 < n) (z : Fin 3 → Circle) (k k' : Cell n) (μ : Fin 3)
    (h : sg n z k μ = sg n z k' μ) : k μ = k' μ := by
  unfold sg at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨m, hm⟩ := h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ)
      = (((th z μ + 2 * Real.pi * ((k' μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ) + (m : ℂ) * (2 * Real.pi) := by
    have := hm
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 : Complex.I * (((th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ)
        = Complex.I * ((((th z μ + 2 * Real.pi * ((k' μ : ℕ) : ℝ)) / (n : ℝ) : ℝ) : ℂ) + (m : ℂ) * (2 * Real.pi)) := by
      rw [this]; ring
    exact mul_left_cancel₀ hI h2
  have h3 : (th z μ + 2 * Real.pi * ((k μ : ℕ) : ℝ)) / (n : ℝ)
      = (th z μ + 2 * Real.pi * ((k' μ : ℕ) : ℝ)) / (n : ℝ) + (m : ℝ) * (2 * Real.pi) := by
    exact_mod_cast h1
  have h4 : ((k μ : ℕ) : ℝ) = ((k' μ : ℕ) : ℝ) + (m : ℝ) * n := by
    field_simp at h3
    nlinarith [Real.pi_pos, h3]
  have h5 : ((k μ : ℕ) : ℤ) = ((k' μ : ℕ) : ℤ) + m * n := by exact_mod_cast h4
  have hk1 := (k μ).isLt
  have hk2 := (k' μ).isLt
  have hm0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : m * (n : ℤ) ≤ -(n : ℤ) := by nlinarith
      omega
    · have : (n : ℤ) ≤ m * n := by nlinarith
      omega
  subst hm0
  apply Fin.ext
  exact_mod_cast (by simpa using h5)

theorem inner_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k k' : Cell n) :
    ⟪pwv n z k, pwv n z k'⟫ = if k = k' then ((n : ℂ) ^ 3) else 0 := by
  classical
  set r : Fin 3 → ℂ := fun μ => (sg n z k μ)⁻¹ * sg n z k' μ with hr
  have hterm : ∀ t : Cell n, ⟪(pwv n z k) t, (pwv n z k') t⟫ = ∏ μ, r μ ^ (t μ : ℕ) := by
    intro t
    simp only [pwv, pw, cc]
    simp only [zpow_natCast]
    rw [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun μ _ => ?_)
    rw [map_pow, ← Complex.inv_eq_conj (norm_sg z k μ), hr]
    simp only []
    rw [mul_pow]
    simp [mul_comm]
  have hsum : ⟪pwv n z k, pwv n z k'⟫ = ∏ μ, ∑ s : Fin n, r μ ^ (s : ℕ) := by
    rw [PiLp.inner_apply]
    simp only [hterm]
    have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n))) (fun μ s => r μ ^ (s : ℕ))
    rw [Fintype.piFinset_univ] at this
    exact this.symm
  have hgeo : ∀ μ, ∑ s : Fin n, r μ ^ (s : ℕ) = if k μ = k' μ then (n : ℂ) else 0 := by
    intro μ
    rw [Fin.sum_univ_eq_sum_range (fun i => r μ ^ i) n]
    by_cases hk : k μ = k' μ
    · have : r μ = 1 := by
        rw [hr]; simp only []
        have : sg n z k μ = sg n z k' μ := by unfold sg; rw [hk]
        rw [← this, inv_mul_cancel₀ (sg_ne z k μ)]
      rw [if_pos hk, this]; simp
    · have hne : r μ ≠ 1 := by
        intro h1
        apply hk
        apply sg_inj hn z k k' μ
        rw [hr] at h1
        simp only [] at h1
        have h2 := sg_ne z k μ
        field_simp at h1
        exact h1.symm
      rw [if_neg hk, geom_sum_eq hne]
      have : r μ ^ n = 1 := by
        rw [hr]; simp only []
        rw [mul_pow, inv_pow, sg_pow hn, sg_pow hn, inv_mul_cancel₀]
        exact Circle.coe_ne_zero (z μ)
      rw [this]; simp
  rw [hsum]
  simp only [hgeo]
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [if_neg hkk]
    have : ∃ μ, k μ ≠ k' μ := by
      by_contra h; push_neg at h; exact hkk (funext h)
    obtain ⟨μ, hμ⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])

end Orth

#print axioms inner_pwv

end AdalyFormal.ScaledCoercivity
