import Mathlib

/-!
# SoPar -- parity obstruction to a block-sum-zero staggering with uniform plaquette weights at odd `ell` (lane sites_only_20261019)

The staggered layer of the ell=2 chain puts angles `θ(x₁, x₂)` on the direction-0 links of the uncovered slice.  The Z-sector reduction (`DpiFull_zfield`) needs the `(0,1)`-plaquette weight
`cos (θ(x₁,x₂) - θ(x₁+1,x₂))` to be the same at all `(x₁,x₂)`, i.e. `θ = τ h` with `h(x₁+1,x₂) = h(x₁,x₂) ± 1`; the first blocked background vanishes iff the sum of `θ` over every aligned
`ell × ell` block of `(x₁,x₂)` vanishes.  `no_uniform_step_blockzero_odd`: for odd `ell` these two requirements are incompatible (already for the two blocks `q = 0, 1` in `x₁`).
-/
set_option autoImplicit false

namespace AdalyFormal.SitesOnly

theorem step_parity (h : ℕ → ℕ → ℤ) (hstep : ∀ x y, h (x + 1) y = h x y + 1 ∨ h (x + 1) y = h x y - 1) :
    ∀ n y, (h n y - h 0 y - (n : ℤ)) % 2 = 0 := by
  intro n y
  induction n with
  | zero => simp
  | succ n ih =>
    rcases hstep n y with e | e <;> rw [e] <;> push_cast <;> omega

theorem no_uniform_step_blockzero_odd (ell : ℕ) (hodd : ell % 2 = 1) (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x + 1) y = h x y + 1 ∨ h (x + 1) y = h x y - 1) :
    ¬ ((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j = 0) ∧
        (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j = 0)) := by
  rintro ⟨h0, h1⟩
  have hd : ∀ i j : ℕ, (h (ell + i) j - h i j - (ell : ℤ)) % 2 = 0 := by
    intro i j
    have a := step_parity h hstep (ell + i) j
    have b := step_parity h hstep i j
    push_cast at a
    omega
  have hsum : (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, (h (ell + i) j - h i j)) = 0 := by
    simp only [Finset.sum_sub_distrib, h0, h1]; ring
  have hz : (((∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, (h (ell + i) j - h i j) : ℤ)) : ZMod 2) = 0 := by
    rw [hsum]; simp
  have hterm : ∀ i j : ℕ, (((h (ell + i) j - h i j : ℤ)) : ZMod 2) = 1 := by
    intro i j
    have := hd i j
    have hodd' : (h (ell + i) j - h i j) % 2 = 1 := by omega
    have e := ZMod.intCast_mod (h (ell + i) j - h i j) 2
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, hodd'] at e
    simpa using e.symm
  simp only [Int.cast_sum, hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hz
  have hell1 : (ell : ZMod 2) = 1 := by
    have := ZMod.natCast_mod ell 2
    rw [hodd] at this
    simpa using this.symm
  rw [hell1] at hz
  simp at hz

/-- **no tunable parameter at odd `ell`** (mean form).  The first blocked background angle is the block MEAN (`ell^-3` times the sum of principal logs, `stridedBlockedGauge`), so with
`θ = τ h + 2π g` it vanishes mod `2π` iff `τ S_q ∈ 2π ell² ℤ` for the integer block sums `S_q` (`q = 0, 1`).  If this held at two parameters `τ₁ ≠ τ₂` with `|τ₁ - τ₂| (|S₀| + |S₁|) < 2π ell²`
(in particular on a whole interval of small width), then `S₀ = S₁ = 0`, which `no_uniform_step_blockzero_odd` excludes. -/
theorem no_nearby_tau_odd (ell : ℕ) (hodd : ell % 2 = 1) (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x + 1) y = h x y + 1 ∨ h (x + 1) y = h x y - 1) (τ₁ τ₂ : ℝ) (hne : τ₁ ≠ τ₂)
    (S₀ S₁ : ℤ) (hS₀ : S₀ = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j)
    (hS₁ : S₁ = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell + i) j)
    (hnear : |τ₁ - τ₂| * (|(S₀ : ℝ)| + |(S₁ : ℝ)|) < 2 * Real.pi * (ell : ℝ) ^ 2)
    (h₁ : ∀ q ∈ ({S₀, S₁} : Set ℤ), ∃ m : ℤ, τ₁ * q = 2 * Real.pi * (ell : ℝ) ^ 2 * m)
    (h₂ : ∀ q ∈ ({S₀, S₁} : Set ℤ), ∃ m : ℤ, τ₂ * q = 2 * Real.pi * (ell : ℝ) ^ 2 * m) : False := by
  have hpi : 0 < 2 * Real.pi * (ell : ℝ) ^ 2 := by
    have : (0 : ℝ) < ell := by
      have : 0 < ell := by omega
      exact_mod_cast this
    positivity
  have key : ∀ S : ℤ, |(S : ℝ)| * |τ₁ - τ₂| < 2 * Real.pi * (ell : ℝ) ^ 2 → (∃ m : ℤ, τ₁ * S = 2 * Real.pi * (ell : ℝ) ^ 2 * m) →
      (∃ m : ℤ, τ₂ * S = 2 * Real.pi * (ell : ℝ) ^ 2 * m) → S = 0 := by
    intro S hlt ⟨m₁, e₁⟩ ⟨m₂, e₂⟩
    by_contra hS
    have hd : (τ₁ - τ₂) * S = 2 * Real.pi * (ell : ℝ) ^ 2 * ((m₁ : ℝ) - m₂) := by linarith
    have habs : |(τ₁ - τ₂) * S| < 2 * Real.pi * (ell : ℝ) ^ 2 := by
      rw [abs_mul, mul_comm]; exact hlt
    rw [hd, abs_mul, abs_of_pos hpi] at habs
    have h1 : |((m₁ : ℝ) - m₂)| < 1 := by
      by_contra hc
      push Not at hc
      nlinarith [abs_nonneg ((m₁ : ℝ) - m₂)]
    have h2 : m₁ = m₂ := by
      have : |m₁ - m₂| < 1 := by exact_mod_cast h1
      have := Int.abs_lt_one_iff.mp this
      omega
    have : (τ₁ - τ₂) * S = 0 := by rw [hd, h2]; simp
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hne (by linarith)
    · exact hS (by exact_mod_cast h0)
  have n0 : |(S₀ : ℝ)| * |τ₁ - τ₂| < 2 * Real.pi * (ell : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (τ₁ - τ₂), abs_nonneg (S₁ : ℝ), mul_nonneg (abs_nonneg (S₁ : ℝ)) (abs_nonneg (τ₁ - τ₂))]
  have n1 : |(S₁ : ℝ)| * |τ₁ - τ₂| < 2 * Real.pi * (ell : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (τ₁ - τ₂), abs_nonneg (S₀ : ℝ), mul_nonneg (abs_nonneg (S₀ : ℝ)) (abs_nonneg (τ₁ - τ₂))]
  have z0 := key S₀ n0 (h₁ S₀ (by simp)) (h₂ S₀ (by simp))
  have z1 := key S₁ n1 (h₁ S₁ (by simp)) (h₂ S₁ (by simp))
  apply no_uniform_step_blockzero_odd ell hodd h hstep
  exact ⟨by rw [← hS₀]; exact z0, by rw [← hS₁]; exact z1⟩

#print axioms no_nearby_tau_odd
#print axioms no_uniform_step_blockzero_odd

end AdalyFormal.SitesOnly
