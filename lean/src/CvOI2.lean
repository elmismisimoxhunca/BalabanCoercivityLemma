import CvOI1

/-!
# CvOI2 -- `fSum` is the sum of `ell^j` consecutive slice values (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset

theorem sum_range_mul' (b : ℕ) (g : ℕ → ℝ) : ∀ a : ℕ,
    ∑ m ∈ range (b * a), g m = ∑ n ∈ range a, ∑ k ∈ range b, g (b * n + k) := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem fSum_eq_sum (ell : ℕ) (f : ℕ → ℝ) : ∀ j v : ℕ, fSum ell j f v = ∑ k ∈ range (ell ^ j), f (v + k) := by
  intro j
  induction j with
  | zero => intro v; simp [fSum]
  | succ j ih =>
    intro v
    have e : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
    rw [e, sum_range_mul' (ell ^ j) (fun m => f (v + m)) ell]
    show ∑ n ∈ range ell, fSum ell j f (v + ell ^ j * n) = _
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ih]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1; ring

#print axioms fSum_eq_sum

end AdalyFormal.CoverOmega
