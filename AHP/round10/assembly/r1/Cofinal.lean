import D1IVT

open Filter
open scoped Topology

namespace AdalyFormal.Round10.Assembly

/-- A nonzero normalized limit forces eventual nonvanishing of the numerator.
No lower bound on the normalization, and no sign, is required. -/
theorem eventually_ne_zero_of_normalized_limit {z s : ℕ → ℝ} {K : ℝ}
    (hK : K ≠ 0) (hlim : Tendsto (fun n => z n / s n) atTop (𝓝 K)) :
    ∀ᶠ n in atTop, z n ≠ 0 := by
  have h : ∀ᶠ n in atTop, z n / s n ≠ 0 :=
    hlim.eventually (eventually_ne_nhds hK)
  filter_upwards [h] with n hn
  intro hz
  apply hn
  simp [hz]

/-- An eventual assertion along an unbounded radius sequence gives a cofinal
assertion in the physical radius. The threshold may depend on every fixed scale. -/
theorem cofinal_of_eventual_subsequence {P : ℕ → Prop} {r : ℕ → ℕ}
    (hr : ∀ n, n ≤ r n) (hP : ∀ᶠ n in atTop, P (r n)) :
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ P R := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  intro R₀
  let n := max R₀ N
  exact ⟨r n, le_trans (le_max_left R₀ N) (hr n), hN n (le_max_right R₀ N)⟩

/-- A useful explicit even-radius progression. -/
theorem even_radius_progression (n : ℕ) :
    n ≤ 2 * (n + 9) ∧ 2 ∣ 2 * (n + 9) ∧ 18 ≤ 2 * (n + 9) := by
  exact ⟨by omega, dvd_mul_right 2 (n + 9), by omega⟩

/-- Nested cofinality does not require a single radius threshold valid for all
scales. This lemma permits any exponent subsequence lying above its index. -/
theorem nested_cofinal_of_eventual {P : ℕ → ℕ → Prop}
    (j : ℕ → ℕ) (r : ℕ → ℕ → ℕ)
    (hj : ∀ n, n ≤ j n) (hr : ∀ n m, m ≤ r n m)
    (hP : ∀ n, ∀ᶠ m in atTop, P (j n) (r n m)) :
    ∀ j₀ : ℕ, ∃ j' : ℕ, j₀ ≤ j' ∧ ∀ R₀ : ℕ,
      ∃ R : ℕ, R₀ ≤ R ∧ P j' R := by
  intro j₀
  exact ⟨j j₀, hj j₀, cofinal_of_eventual_subsequence (hr j₀) (hP j₀)⟩

#print axioms eventually_ne_zero_of_normalized_limit
#print axioms cofinal_of_eventual_subsequence
#print axioms even_radius_progression
#print axioms nested_cofinal_of_eventual

end AdalyFormal.Round10.Assembly
