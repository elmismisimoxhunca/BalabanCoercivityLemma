import D1IVT

/-!
Finite-dimensional invertible transfer dynamics: an observed orbit is either identically
zero or nonzero cofinally. No eigenvalues or explicit recurrence coefficients are needed.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing

section Transfer
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- In finite dimension, an injective transfer map preserves an invariant subspace backwards. -/
theorem invariant_backward (T : E →ₗ[K] E) (hT : Function.Injective T)
    (P : Submodule K E) (hP : ∀ x ∈ P, T x ∈ P)
    (x : E) (hx : T x ∈ P) : x ∈ P := by
  have hk : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr hT
  have he : P.comap T = P := by
    rw [LinearMap.comap_eq_sup_ker_of_disjoint hP (by simp [hk]), hk, sup_bot_eq]
  have hm : x ∈ P.comap T := hx
  rwa [he] at hm

/-- Vanishing of a linear observable on an entire tail forces vanishing on the whole orbit. -/
theorem transfer_eq_zero_of_zero_tail (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (N : ℕ)
    (hz : ∀ n, N ≤ n → L ((T ^ n) x) = 0) : ∀ n, L ((T ^ n) x) = 0 := by
  let P : Submodule K E := ⨅ n : ℕ, LinearMap.ker (L.comp (T ^ n))
  have hmem (y : E) : y ∈ P ↔ ∀ n, L ((T ^ n) y) = 0 := by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  have hP : ∀ y ∈ P, T y ∈ P := by
    intro y hy
    rw [hmem] at hy ⊢
    intro n
    simpa only [pow_succ, Module.End.mul_apply] using hy (n + 1)
  have hback : ∀ n (y : E), (T ^ n) y ∈ P → y ∈ P := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
        intro y hy
        apply invariant_backward T hT P hP y
        apply ih (T y)
        simpa only [pow_succ, Module.End.mul_apply] using hy
  have htail : (T ^ N) x ∈ P := by
    rw [hmem]
    intro n
    simpa only [pow_add, Module.End.mul_apply] using hz (n + N) (by omega)
  exact (hmem x).mp (hback N x htail)

/-- A single observed nonzero value supplies infinitely many, with no sign requirement. -/
theorem transfer_cofinal_nonzero (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (k : ℕ) (hk : L ((T ^ k) x) ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ L ((T ^ n) x) ≠ 0 := by
  intro N
  by_contra h
  push Not at h
  exact hk (transfer_eq_zero_of_zero_tail T hT L x N h k)

/-- Nonzero denominators do not matter; one may work with an unnormalized numerator. -/
theorem transfer_quotient_cofinal_nonzero (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (denominator scalar : ℕ → K)
    (hd : ∀ n, denominator n ≠ 0)
    (hform : ∀ n, scalar n = L ((T ^ n) x) / denominator n)
    (k : ℕ) (hk : scalar k ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ scalar n ≠ 0 := by
  have hseed : L ((T ^ k) x) ≠ 0 := by
    intro hz
    apply hk
    rw [hform, hz, zero_div]
  intro N
  obtain ⟨n, hn, hne⟩ := transfer_cofinal_nonzero T hT L x k hseed N
  refine ⟨n, hn, ?_⟩
  rw [hform]
  exact div_ne_zero hne (hd n)

/-- A sampled arithmetic progression is itself an invertible transfer system. -/
theorem transfer_progression_cofinal_nonzero (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (step offset k : ℕ)
    (hk : L ((T ^ (step * k + offset)) x) ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ L ((T ^ (step * n + offset)) x) ≠ 0 := by
  have hpower (n : ℕ) : ((T ^ step) ^ n) ((T ^ offset) x) =
      (T ^ (step * n + offset)) x := by
    rw [pow_add, pow_mul, Module.End.mul_apply]
  have hinjall : ∀ m : ℕ, Function.Injective (T ^ m) := by
    intro m
    induction m with
    | zero => intro a b hab; exact hab
    | succ m ih =>
        intro a b hab
        apply hT
        apply ih
        simpa only [pow_succ, Module.End.mul_apply] using hab
  have hinj := hinjall step
  have hs : L (((T ^ step) ^ k) ((T ^ offset) x)) ≠ 0 := by rwa [hpower]
  intro N
  obtain ⟨n, hn, hne⟩ := transfer_cofinal_nonzero (T ^ step) hinj L ((T ^ offset) x) k hs N
  exact ⟨n, hn, by rwa [hpower] at hne⟩

end Transfer

#print axioms invariant_backward
#print axioms transfer_eq_zero_of_zero_tail
#print axioms transfer_cofinal_nonzero
#print axioms transfer_quotient_cofinal_nonzero
#print axioms transfer_progression_cofinal_nonzero

end AdalyFormal.Round10.Nonvanishing
