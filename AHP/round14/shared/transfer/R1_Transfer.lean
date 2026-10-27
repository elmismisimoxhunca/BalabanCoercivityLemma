import DrEquiv

/-!
Exact algebra for constant-coefficient two-layer transfer.

Nothing in this file is a dictionary for the frozen lattice operators.  The
interface is deliberately scalar and explicit so that a physical collar
calculation can supply its coefficients without any asymptotic or numerical
premise.
-/
set_option autoImplicit false

namespace AdalyFormal.Round14.Transfer

noncomputable section

open Polynomial

/-- A two-branch scalar mode.  On the collar one normally has `r = ρ^2` for a
quadratic observation, or `r = ρ` for a linear one. -/
def mode (r a b : ℝ) (n : ℕ) : ℝ := a * r^n + b * (r⁻¹)^n

/-- The oriented area of two scalar sequences on adjacent layers. -/
def orientedArea (x y : ℕ → ℝ) (n : ℕ) : ℝ := x n * y (n+1) - y n * x (n+1)

/-- Every two-branch mode solves the constant reversible two-layer recurrence. -/
theorem mode_recurrence {r : ℝ} (hr : r ≠ 0) (a b : ℝ) (n : ℕ) :
    mode r a b (n+2) = (r+r⁻¹) * mode r a b (n+1) - mode r a b n := by
  simp only [mode, pow_succ, inv_pow]
  field_simp [pow_ne_zero n hr, pow_ne_zero (n+1) hr]
  ring

/-- The oriented area of two-branch modes is constant.  Its coefficient is the
ordinary determinant of the two pairs of mode amplitudes. -/
theorem mode_orientedArea {r : ℝ} (hr : r ≠ 0) (a b c d : ℝ) (n : ℕ) :
    orientedArea (mode r a b) (mode r c d) n = (a*d-b*c) * (r⁻¹-r) := by
  simp only [orientedArea, mode, pow_succ, inv_pow]
  field_simp [pow_ne_zero n hr, pow_ne_zero (n+1) hr]
  ring

/-- A nonzero amplitude determinant and nondegenerate transfer root propagate a
nonzero oriented area to every collar layer. -/
theorem mode_orientedArea_ne_zero {r : ℝ} (hr : r ≠ 0)
    (hroot : r⁻¹-r ≠ 0) {a b c d : ℝ} (hseed : a*d-b*c ≠ 0) (n : ℕ) :
    orientedArea (mode r a b) (mode r c d) n ≠ 0 := by
  rw [mode_orientedArea hr]
  exact mul_ne_zero hseed hroot

/-- The general three-term Laurent value associated with a quadratic observable
on two-branch data.  `A` is the decaying-square coefficient, `B` the mixed
coefficient, and `C` the growing-square coefficient. -/
def laurent (r A B C : ℝ) (n : ℕ) : ℝ := A*r^n+B+C*(r⁻¹)^n

/-- A nonzero real polynomial is eventually nonzero on any injective sequence. -/
theorem eval_ne_zero_eventually {K : Type*} [Field K]
    (p : K[X]) (hp : p ≠ 0) (a : ℕ → K) (ha : Function.Injective a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (a n) ≠ 0 := by
  have hfin : Set.Finite (a ⁻¹' {x : K | p.IsRoot x}) :=
    Set.Finite.preimage (fun _ _ _ _ h => ha h) (Polynomial.finite_setOf_isRoot hp)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N+1, fun n hn hzero => ?_⟩
  have hnN : n ≤ N := hN hzero
  omega

/-- Clearing the decaying denominator gives a quadratic polynomial. -/
def laurentPolynomial (A B C : ℝ) : ℝ[X] :=
  Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C

theorem laurentPolynomial_ne_zero {A B C : ℝ}
    (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) : laurentPolynomial A B C ≠ 0 := by
  intro hp
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hp
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hp
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hp
  simp [laurentPolynomial] at h0 h1 h2
  rcases h with hA | hB | hC
  · exact hA h2
  · exact hB h1
  · exact hC h0

/-- Exact polynomial certificate after multiplication by `r^n`. -/
theorem laurent_mul_pow {r : ℝ} (hr : r ≠ 0) (A B C : ℝ) (n : ℕ) :
    r^n * laurent r A B C n = (laurentPolynomial A B C).eval (r^n) := by
  have hp : r^n * (r⁻¹)^n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hr, one_pow]
  simp only [laurent, laurentPolynomial, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  calc
    _ = A*(r^n)^2+B*r^n+C*(r^n*(r⁻¹)^n) := by ring
    _ = _ := by rw [hp]; ring

/-- Any nonzero Laurent coefficient, not only the leading one, gives eventual
nonvanishing.  This also covers an exponentially smaller remainder. -/
theorem laurent_eventually_ne_zero {r A B C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → laurent r A B C n ≠ 0 := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have ha : Function.Injective (fun n : ℕ => r^n) :=
    (pow_right_strictAnti₀ hr0 hr1).injective
  obtain ⟨N, hN⟩ := eval_ne_zero_eventually (laurentPolynomial A B C)
    (laurentPolynomial_ne_zero h) (fun n : ℕ => r^n) ha
  refine ⟨N, fun n hn hz => hN n hn ?_⟩
  rw [← laurent_mul_pow hr A B C n, hz, mul_zero]

/-- Cofinal form used by radius and sparse-subsequence arguments. -/
theorem laurent_cofinal_ne_zero {r A B C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ laurent r A B C n ≠ 0 := by
  obtain ⟨N₀, hN₀⟩ := laurent_eventually_ne_zero hr0 hr1 h
  intro N
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

/-- The intended dominant-seed specialization. -/
theorem laurent_eventually_ne_zero_of_lead {r A B C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hA : A ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → laurent r A B C n ≠ 0 :=
  laurent_eventually_ne_zero hr0 hr1 (Or.inl hA)

/-- Exact interface for an observable on the admissible even-radius
progression `R = 2*(n+9)`.  A physical transfer dictionary must provide this
identity and one nonzero Laurent coefficient; no numerical seed is involved. -/
def RadiusLaurentData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r A B C : ℝ, 0 < r ∧ r < 1 ∧ (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
    ∀ n : ℕ, observable q (2*(n+9)) = laurent r A B C n

/-- A Laurent certificate gives arbitrarily large admissible even radii with a
nonzero observable. -/
theorem radius_cofinal_nonzero_of_laurent (observable : ℕ → ℕ → ℝ) (q : ℕ)
    (h : RadiusLaurentData observable q) :
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ observable q R ≠ 0 := by
  obtain ⟨r,A,B,C,hr0,hr1,hcoef,hform⟩ := h
  intro R₀
  obtain ⟨n,hn,hz⟩ := laurent_cofinal_ne_zero hr0 hr1 hcoef R₀
  refine ⟨2*(n+9), by omega, ⟨n+9,rfl⟩, by omega, ?_⟩
  rwa [hform n]

/-- Scale-indexed certificates for the original nested dyadic/even order. -/
def DyadicLaurentData (observable : ℕ → ℕ → ℝ) : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ RadiusLaurentData observable (2^j)

/-- The nested cofinal conclusion, with no interchange of the scale and radius
quantifiers. -/
theorem dyadic_cofinal_nonzero_of_laurent (observable : ℕ → ℕ → ℝ)
    (h : DyadicLaurentData observable) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ observable (2^j) R ≠ 0 := by
  intro j₀
  obtain ⟨j,hj,hd⟩ := h j₀
  exact ⟨j,hj,radius_cofinal_nonzero_of_laurent observable (2^j) hd⟩

#print axioms mode
#print axioms orientedArea
#print axioms mode_recurrence
#print axioms mode_orientedArea
#print axioms mode_orientedArea_ne_zero
#print axioms laurent
#print axioms eval_ne_zero_eventually
#print axioms laurentPolynomial
#print axioms laurentPolynomial_ne_zero
#print axioms laurent_mul_pow
#print axioms laurent_eventually_ne_zero
#print axioms laurent_cofinal_ne_zero
#print axioms laurent_eventually_ne_zero_of_lead
#print axioms RadiusLaurentData
#print axioms radius_cofinal_nonzero_of_laurent
#print axioms DyadicLaurentData
#print axioms dyadic_cofinal_nonzero_of_laurent

end
end AdalyFormal.Round14.Transfer
