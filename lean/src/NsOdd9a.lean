import NsOdd8c

/-!
# NsOdd9a -- real inequalities for the unit-level loops (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false

theorem b2_range {ell : ℕ} (h5 : 5 ≤ ell) : 0 ≤ b2 ell ∧ b2 ell ≤ 1 := by
  have hl : (5 : ℝ) ≤ ell := by exact_mod_cast h5
  have h0 : (0 : ℝ) < ell := by linarith
  unfold b2
  constructor
  · have h1 : ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : ((ell : ℝ) - 1) / (ell : ℝ) ^ 4 ≤ ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have h1' : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
      have : (ell : ℝ) ^ 4 = (ell : ℝ) ^ 2 * (ell : ℝ) ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg (ell : ℝ)]
    linarith
  · have h1 : 0 ≤ ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 := by apply div_nonneg <;> [linarith; positivity]
    have h2 : 0 ≤ ((ell : ℝ) - 1) / (ell : ℝ) ^ 4 := by apply div_nonneg <;> [linarith; positivity]
    linarith

theorem d2_range {ell : ℕ} (h5 : 5 ≤ ell) : 0 ≤ d2 ell ∧ d2 ell ≤ 1 / 2 := by
  have hl : (5 : ℝ) ≤ ell := by exact_mod_cast h5
  have h0 : (0 : ℝ) < ell := by linarith
  unfold d2
  constructor
  · apply div_nonneg
    · apply mul_nonneg <;> [linarith; positivity]
    · positivity
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (ell : ℝ), mul_pos h0 h0]

/-- direction 1. -/
theorem unit1_real (b d I0 Ix pm1 q1 : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1 / 2)
    (hI0 : I0 = 0 ∨ I0 = 1) (hIx : Ix = 0 ∨ Ix = 1) (hpm : (pm1 = 1 ∧ q1 = 0) ∨ (pm1 = -1 ∧ q1 = 1)) :
    |2 * q1 * (b * I0) + pm1 * (b * Ix) - b * I0 + pm1 * (I0 - Ix) * (d + d)| ≤ 1 := by
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hd0, hd1⟩ := hd
  rcases hI0 with h | h <;> rcases hIx with h' | h' <;> rcases hpm with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst h h' hp hq <;>
    (rw [abs_le]; constructor <;> nlinarith)

/-- direction 0. -/
theorem unit0_real (b d X q1 pm1 : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1 / 2)
    (hX : X = -1 ∨ X = 0 ∨ X = 1) (hpm : (pm1 = 1 ∧ q1 = 0) ∨ (pm1 = -1 ∧ q1 = 1)) :
    |q1 * (b * X) + (X * (pm1 * d - d))| ≤ 1 := by
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hd0, hd1⟩ := hd
  rcases hX with h | h | h <;> rcases hpm with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst h hp hq <;> (rw [abs_le]; constructor <;> nlinarith)

end AdalyFormal.CoverOmega
