import D1IVT

/-! A check on the free-profile strategy, NOT a counterexample to the actual
coupling premise. Pointwise profile detection does not imply a single definite
profile on a whole kernel, even for U(1)-invariant quadratic forms. -/
set_option autoImplicit false
namespace AdalyFormal.Round10.Assembly.ProfileQuantifiers

noncomputable def form (a b c : ℝ) (z w : ℂ) : ℝ :=
  a * (Complex.normSq z - Complex.normSq w) +
    b * (2 * (star z * w).re) + c * (2 * (star z * w).im)

/-- Common complex scalar multiplication preserves the form up to norm squared. -/
theorem form_scale (a b c : ℝ) (g z w : ℂ) :
    form a b c (g*z) (g*w) = Complex.normSq g * form a b c z w := by
  simp only [form, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- In particular the family has the same common U(1) symmetry as charged blocks. -/
theorem form_U1 (a b c : ℝ) (g z w : ℂ) (hg : Complex.normSq g = 1) :
    form a b c (g*z) (g*w) = form a b c z w := by
  rw [form_scale, hg, one_mul]

/-- A profile chosen from the vector detects it strictly positively. -/
theorem self_profile (z w : ℂ) :
    form (Complex.normSq z - Complex.normSq w)
      (2 * (star z * w).re) (2 * (star z * w).im) z w =
      (Complex.normSq z + Complex.normSq w)^2 := by
  simp only [form, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem every_vector_has_profile (z w : ℂ) (hne : z ≠ 0 ∨ w ≠ 0) :
    ∃ a b c : ℝ, 0 < form a b c z w := by
  refine ⟨Complex.normSq z - Complex.normSq w,
    2 * (star z * w).re, 2 * (star z * w).im, ?_⟩
  rw [self_profile]
  have hn : 0 < Complex.normSq z + Complex.normSq w := by
    rcases hne with hz | hw
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hz) (Complex.normSq_nonneg w)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) (Complex.normSq_pos.mpr hw)
  exact sq_pos_of_pos hn

/-- No profile is definite on the two-complex-dimensional space: the coordinate
vectors have opposite values a and -a. Thus the quantifiers cannot be swapped. -/
theorem no_profile_definite (a b c : ℝ) :
    ¬ ((∀ z w : ℂ, z ≠ 0 ∨ w ≠ 0 → 0 < form a b c z w) ∨
       (∀ z w : ℂ, z ≠ 0 ∨ w ≠ 0 → form a b c z w < 0)) := by
  intro h
  rcases h with hp | hn
  · have h1 := hp 1 0 (Or.inl one_ne_zero)
    have h2 := hp 0 1 (Or.inr one_ne_zero)
    norm_num [form] at h1 h2
    linarith
  · have h1 := hn 1 0 (Or.inl one_ne_zero)
    have h2 := hn 0 1 (Or.inr one_ne_zero)
    norm_num [form] at h1 h2
    linarith

#print axioms form
#print axioms form_scale
#print axioms form_U1
#print axioms self_profile
#print axioms every_vector_has_profile
#print axioms no_profile_definite
end AdalyFormal.Round10.Assembly.ProfileQuantifiers
