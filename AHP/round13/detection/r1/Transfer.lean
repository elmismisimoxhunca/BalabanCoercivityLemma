import DrEquiv
set_option autoImplicit false

/-! Two-layer unique continuation and the stronger determinant propagation test.
These are algebraic tools, not a frozen-carrier dictionary or a proof of P3. -/
namespace AdalyFormal.Round13.Detection.Transfer

section Vector
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Two adjacent zero layers propagate one step to the left if the oldest
coefficient is nonzero. The coefficient of the middle layer may vary. -/
theorem zero_pair_step (a b : ℕ → K) (u : ℕ → E) (n : ℕ)
    (hb : b n ≠ 0)
    (hr : u (n+2) = a n • u (n+1) + b n • u n)
    (h1 : u (n+1) = 0) (h2 : u (n+2) = 0) : u n = 0 := by
  rw [h1, h2, smul_zero, zero_add] at hr
  exact (smul_eq_zero.mp hr.symm).resolve_left hb

/-- Finite collar version: no recurrence beyond the observation layer is assumed. -/
theorem zero_prefix_of_zero_pair (a b : ℕ → K) (u : ℕ → E) (N : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hr : ∀ n < N, u (n+2) = a n • u (n+1) + b n • u n)
    (h0 : u N = 0) (h1 : u (N+1) = 0) : ∀ k ≤ N+1, u k = 0 := by
  induction N with
  | zero =>
    intro k hk
    interval_cases k <;> assumption
  | succ N ih =>
    have hN : u N = 0 := zero_pair_step a b u N (hb N (by omega))
      (hr N (by omega)) h0 h1
    have hp := ih (fun n hn => hb n (by omega))
      (fun n hn => hr n (by omega)) hN h0
    intro k hk
    by_cases h : k ≤ N+1
    · exact hp k h
    · have he : k = N+1+1 := by omega
      subst k
      exact h1

/-- A nonzero source-side layer forbids simultaneous vanishing of two interface
layers. It says nothing about a quadratic jet of those layers. -/
theorem pair_ne_zero_of_seed (a b : ℕ → K) (u : ℕ → E) (N k : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hr : ∀ n < N, u (n+2) = a n • u (n+1) + b n • u n)
    (hk : k ≤ N+1) (hne : u k ≠ 0) : u N ≠ 0 ∨ u (N+1) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hne (zero_prefix_of_zero_pair a b u N hb hr h.1 h.2 k hk)
end Vector

section Determinant
variable {K : Type*} [Field K]

/-- Oriented two-color area, not merely the size of a linear interface trace. -/
def area (x y : ℕ → K) (n : ℕ) : K := x n * y (n+1) - y n * x (n+1)

/-- The area obeys a first-order nonvanishing law if both components satisfy
the SAME real/scalar recurrence. The physical identification is separate. -/
theorem area_step (a b x y : ℕ → K) (n : ℕ)
    (hx : x (n+2) = a n * x (n+1) + b n * x n)
    (hy : y (n+2) = a n * y (n+1) + b n * y n) :
    area x y (n+1) = -b n * area x y n := by
  unfold area
  rw [show n+1+1 = n+2 by omega, hx, hy]
  ring

/-- A nonzero AREA seed, unlike a nonzero vector seed, propagates to a nonzero
quadratic observable at every finite collar layer. -/
theorem area_ne_zero (a b x y : ℕ → K) (N : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hx : ∀ n < N, x (n+2) = a n * x (n+1) + b n * x n)
    (hy : ∀ n < N, y (n+2) = a n * y (n+1) + b n * y n)
    (hseed : area x y 0 ≠ 0) : area x y N ≠ 0 := by
  induction N with
  | zero => exact hseed
  | succ N ih =>
    rw [area_step a b x y N (hx N (by omega)) (hy N (by omega))]
    exact mul_ne_zero (neg_ne_zero.mpr (hb N (by omega)))
      (ih (fun n hn => hb n (by omega)) (fun n hn => hx n (by omega))
        (fun n hn => hy n (by omega)))

/-- Collinear colors have zero area regardless of a nonzero linear trace. -/
theorem area_proportional_zero (x : ℕ → K) (c : K) (n : ℕ) :
    area x (fun k => c * x k) n = 0 := by
  unfold area
  ring
end Determinant

/-- An exact exponentially decaying, everywhere-nonzero collar solution can have
zero oriented quadratic trace at EVERY layer. This is not a crossing vector. -/
theorem decaying_trace_counterexample :
    ∃ x y : ℕ → ℝ,
      (∀ n, x n ≠ 0) ∧
      (∀ n, x (n+2) = (5/2:ℝ) * x (n+1) - x n) ∧
      (∀ n, y (n+2) = (5/2:ℝ) * y (n+1) - y n) ∧
      (∀ n, area x y n = 0) := by
  refine ⟨fun n => (1/2:ℝ)^n, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro n
    exact pow_ne_zero n (by norm_num)
  · intro n
    simp only [pow_succ, pow_add]
    ring
  · intro n
    ring
  · intro n
    simp [area]

#print axioms zero_pair_step
#print axioms zero_prefix_of_zero_pair
#print axioms pair_ne_zero_of_seed
#print axioms area_step
#print axioms area_ne_zero
#print axioms area_proportional_zero
#print axioms decaying_trace_counterexample
end AdalyFormal.Round13.Detection.Transfer
