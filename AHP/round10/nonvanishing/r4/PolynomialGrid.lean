import D1IVT

/-!
A finite algebraic certificate for nested cofinal nonvanishing.
These are abstract block lemmas, NOT certificates for the frozen crossing operators.
A polynomial certificate must still be supplied from those operators.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.Round10.Nonvanishing.PolynomialGrid

open Polynomial

/-- A nonzero polynomial has no roots sufficiently far along any injective sequence. -/
theorem eval_ne_zero_eventually {K : Type*} [Field K]
    (p : K[X]) (hp : p ≠ 0) (a : ℕ → K) (ha : Function.Injective a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (a n) ≠ 0 := by
  have hfin : Set.Finite (a ⁻¹' {x : K | p.IsRoot x}) :=
    Set.Finite.preimage (fun _ _ _ _ h => ha h) (Polynomial.finite_setOf_isRoot hp)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn hzero => ?_⟩
  have hnN : n ≤ N := hN hzero
  omega

/-- The outer variable is the radius variable; coefficients are scale polynomials. -/
noncomputable def specialize {K : Type*} [CommRing K] (p : K[X][X]) (x : K) : K[X] :=
  p.map (Polynomial.evalRingHom x)

noncomputable def evalTwo {K : Type*} [CommRing K] (p : K[X][X]) (x y : K) : K :=
  (specialize p x).eval y

theorem evalTwo_eq_eval₂ {K : Type*} [CommRing K] (p : K[X][X]) (x y : K) :
    evalTwo p x y = p.eval₂ (Polynomial.evalRingHom x) y := by
  exact (Polynomial.eval₂_eq_eval_map _).symm

/-- Only finitely many scale specializations can be the zero polynomial. -/
theorem specialize_ne_zero_eventually {K : Type*} [Field K]
    (p : K[X][X]) (hp : p ≠ 0) (a : ℕ → K) (ha : Function.Injective a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → specialize p (a n) ≠ 0 := by
  have hc : ∃ i : ℕ, p.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply Polynomial.ext
    intro i
    simpa using h i
  obtain ⟨i, hi⟩ := hc
  obtain ⟨N, hN⟩ := eval_ne_zero_eventually (p.coeff i) hi a ha
  refine ⟨N, fun n hn hz => hN n hn ?_⟩
  have hc := congrArg (fun r : K[X] => r.coeff i) hz
  simpa [specialize] using hc

/-- Nested, not diagonal, avoidance of the zero locus of a nonzero bivariate polynomial. -/
theorem grid_ne_zero_eventually {K : Type*} [Field K]
    (p : K[X][X]) (hp : p ≠ 0)
    (a : ℕ → K) (ha : Function.Injective a)
    (b : ℕ → ℕ → K) (hb : ∀ j, Function.Injective (b j)) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      evalTwo p (a j) (b j n) ≠ 0 := by
  obtain ⟨J, hJ⟩ := specialize_ne_zero_eventually p hp a ha
  exact ⟨J, fun j hj => eval_ne_zero_eventually (specialize p (a j))
    (hJ j hj) (b j) (hb j)⟩

theorem dyadic_argument_injective {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Function.Injective (fun j : ℕ => ρ ^ (2 ^ j)) := by
  exact (pow_right_strictAnti₀ hρ hρ1).injective.comp
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)))

theorem radius_argument_injective {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (j : ℕ) :
    Function.Injective (fun R : ℕ => ρ ^ ((2 ^ j) * R)) := by
  intro R S h
  have hs := (pow_right_strictAnti₀ hρ hρ1).injective h
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ j) hs

/-- This supplies all large exponents, then all large radii at each exponent. -/
theorem geometric_grid_ne_zero_eventually (p : ℝ[X][X]) (hp : p ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      evalTwo p (ρ ^ (2 ^ j)) (ρ ^ ((2 ^ j) * R)) ≠ 0 :=
  grid_ne_zero_eventually p hp _ (dyadic_argument_injective hρ hρ1)
    _ (radius_argument_injective hρ hρ1)

/-- One exact seed, even off the physical grid, proves the certificate is not identically zero. -/
theorem geometric_grid_ne_zero_of_seed (p : ℝ[X][X]) (x₀ y₀ : ℝ)
    (hseed : evalTwo p x₀ y₀ ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      evalTwo p (ρ ^ (2 ^ j)) (ρ ^ ((2 ^ j) * R)) ≠ 0 := by
  have hp : p ≠ 0 := by
    intro hz
    apply hseed
    simp [hz, evalTwo, specialize]
  obtain ⟨J, hJ⟩ := geometric_grid_ne_zero_eventually p hp hρ hρ1
  intro j₀
  let j := max J j₀
  obtain ⟨N, hN⟩ := hJ j (le_max_left _ _)
  refine ⟨j, le_max_right _ _, fun R₀ => ?_⟩
  let R := 2 * (N + R₀ + 9)
  refine ⟨R, ?_, ⟨N + R₀ + 9, rfl⟩, ?_, hN R ?_⟩ <;> omega

#print axioms eval_ne_zero_eventually
#print axioms specialize
#print axioms evalTwo
#print axioms evalTwo_eq_eval₂
#print axioms specialize_ne_zero_eventually
#print axioms grid_ne_zero_eventually
#print axioms dyadic_argument_injective
#print axioms radius_argument_injective
#print axioms geometric_grid_ne_zero_eventually
#print axioms geometric_grid_ne_zero_of_seed

end AdalyFormal.Round10.Nonvanishing.PolynomialGrid
