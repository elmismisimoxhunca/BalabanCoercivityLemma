import NtCvOF15

/-!
# NtTwo -- why the nested witness family does not reach `ell = 2` (lane ncwdh_small_ell_20261018)

The witness competitor of the nested chain is `zfun (gU M R p)`: a direction-1 bond field whose profile `g` depends on the coordinate `x₀` only.  It must satisfy
(i) `g u = 0` at `ell`-aligned positions `u` (those direction-1 bonds lie on the staircase paths of `Λ~`; see `zfun_gU_eq_zero_of_dir`, `onLambdaTildeIn_gU`), and
(ii) `∑_{n < ell} g (ell q + n) = 0` for every `q` (`gU_block`, used to kill `Q₁` on the field).

* `AdmProfile ell g` : (i) and (ii).
* `admProfile_two` : for `ell = 2`, `AdmProfile 2 g` forces `g u = 0` for every `u` (so no nonzero x₀-profile exists).
* `admProfile_three` : for `ell = 3` the profile `δ₁ - δ₂` on each block is admissible and nonzero (the case now covered).
* `gU_not_adm_two` : the witness profile `gU M R p` is not admissible for `ell = 2`, for every `M, R, p` (in particular `gU_block` cannot hold there together with the aligned-vanishing).
-/
set_option autoImplicit false

namespace AdalyFormal.CoverOmega.Win2

open Finset

/-- the constraints on an `x₀`-profile of the witness field. -/
def AdmProfile (ell : ℕ) (g : ℕ → ℝ) : Prop :=
  (∀ u, u % ell = 0 → g u = 0) ∧ ∀ q, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0

theorem admProfile_two {g : ℕ → ℝ} (h : AdmProfile 2 g) : ∀ u, g u = 0 := by
  obtain ⟨h1, h2⟩ := h
  intro u
  have hq := h2 (u / 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, add_zero] at hq
  have he : g (2 * (u / 2)) = 0 := h1 _ (by omega)
  rw [he, zero_add] at hq
  by_cases hu : u % 2 = 0
  · exact h1 u hu
  · have : u = 2 * (u / 2) + 1 := by omega
    rw [this]; exact hq

theorem admProfile_three : ∃ g : ℕ → ℝ, AdmProfile 3 g ∧ ∃ u, g u ≠ 0 := by
  refine ⟨fun u => if u % 3 = 1 then 1 else if u % 3 = 2 then -1 else 0, ⟨?_, ?_⟩, 1, ?_⟩
  · intro u hu; simp [hu]
  · intro q
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have a0 : (3 * q + 0) % 3 = 0 := by omega
    have a1 : (3 * q + 1) % 3 = 1 := by omega
    have a2 : (3 * q + 2) % 3 = 2 := by omega
    simp [a0, a1, a2]
  · norm_num

variable [CfData]

/-- the witness profile `gU M R p` is nonzero (at `u0N M R + p`), so by `admProfile_two` it is not admissible for `ell = 2` (for any `M, R, p`):
for `u0N + p` even its support point is aligned (violates (i)); for `u0N + p` odd the two support points lie in different 2-blocks (violates (ii)). -/
theorem gU_not_adm_two (M R p : ℕ) : ¬ AdmProfile 2 (gU M R p) := by
  intro h
  have h0 := admProfile_two h (u0N M R + p)
  unfold gU at h0
  simp at h0

#print axioms admProfile_two
#print axioms admProfile_three
#print axioms gU_not_adm_two

end AdalyFormal.CoverOmega.Win2
