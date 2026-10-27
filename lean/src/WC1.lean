import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# WC1 -- abstract perturbation lemma (M2 W6 lane)

`T = id + N + S`, `N ∘ N = 0`, `ν(N y) ≤ A ν(y)`, `ν(S y) ≤ s ν(y)`, `2 s (1 + A) < 1` ⇒ `T` injective.
(`(I - N) T = I + S - N S`.)  Pure linear algebra; `ν` is any "squared seminorm-like" gauge.
-/
set_option autoImplicit false

namespace AdalyFormal.M2W6

theorem inj_of_perturbed {H : Type*} [AddCommGroup H] [Module ℝ H] (ν : H → ℝ)
    (hν0 : ∀ x, 0 ≤ ν x) (hνadd : ∀ x y, ν (x + y) ≤ 2 * ν x + 2 * ν y) (hνneg : ∀ x, ν (-x) = ν x)
    (hνzero : ∀ x, ν x ≤ 0 → x = 0)
    (N S T : H →ₗ[ℝ] H) (hT : ∀ y, T y = y + N y + S y) (hNN : ∀ y, N (N y) = 0)
    (A s : ℝ) (hN : ∀ y, ν (N y) ≤ A * ν y) (hS : ∀ y, ν (S y) ≤ s * ν y) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hsmall : 2 * s * (1 + A) < 1) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have h0 : y + N y + S y = 0 := by rw [← hT]; exact hy
  have h1 : N y + N (N y) + N (S y) = 0 := by
    have := congrArg N h0
    simpa [map_add] using this
  rw [hNN, add_zero] at h1
  have hNy : N y = -(N (S y)) := eq_neg_of_add_eq_zero_left h1
  have hy' : y = N (S y) + -(S y) := by
    calc y = (y + N y + S y) + (-(N y)) + (-(S y)) := by abel
      _ = 0 + N (S y) + (-(S y)) := by rw [h0, hNy, neg_neg]
      _ = N (S y) + -(S y) := by abel
  have h2 : ν y ≤ 2 * ν (N (S y)) + 2 * ν (-(S y)) := by
    conv_lhs => rw [hy']
    exact hνadd _ _
  rw [hνneg] at h2
  have h3 : ν (N (S y)) ≤ A * (s * ν y) := (hN (S y)).trans (mul_le_mul_of_nonneg_left (hS y) hA)
  have h4 := hS y
  have hy0 := hν0 y
  have : ν y ≤ 0 := by nlinarith [mul_nonneg hA hs, mul_nonneg hs hy0, mul_nonneg (mul_nonneg hA hs) hy0]
  exact hνzero y this

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.inj_of_perturbed
