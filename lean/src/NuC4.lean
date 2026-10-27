import NuC3

/-!
# NuC4 -- `uc_rows`: a flux-zero state at one interior row forces the whole vector to vanish; `pair_lemma` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi

section
variable {R a b : ℕ} {st : ℕ → ℤ} {ln : ℕ → ℕ} {e f W : ℤ → ℝ} {μ : ℕ → ℝ}

theorem uc_rows (hW : ∀ y, W y ≠ 0) (hf : ∀ y, f y = W y * (e (y + 1) - e y))
    (hstS : ∀ i, st (i + 1) = st i + ln i) (hlnL : ∀ i, i < a → ln i = 1)
    (hlnI : ∀ i, a ≤ i → i + b < R → 2 ≤ ln i) (hlnR : ∀ i, R ≤ i + b → i < R → ln i = 1)
    (hint : ∀ i, i < R → ∀ j : ℕ, j + 1 < ln i → W (st i + j) = 1)
    (hEL : ∀ i, i < R → ∀ j : ℕ, j < ln i → f (st i + j - 1) - f (st i + j) = μ i)
    (hS : ∀ i, i < R → ∑ j ∈ Finset.range (ln i), e (st i + j) = 0)
    {i1 : ℕ} (ha : a ≤ i1) (hb : i1 + b < R) (hz : FSt e f (st i1)) :
    ∀ i, i < R → ∀ j : ℕ, j < ln i → e (st i + j) = 0 := by
  -- singleton rows
  have hsingle : ∀ i, i < R → ln i = 1 → e (st i) = 0 := by
    intro i hi hl
    have := hS i hi
    rw [hl] at this
    simpa using this
  -- forward
  have hfwd : ∀ d : ℕ, i1 + d + b ≤ R → FSt e f (st (i1 + d)) ∧
      ∀ i, i1 ≤ i → i < i1 + d → ∀ j : ℕ, j < ln i → e (st i + j) = 0 := by
    intro d
    induction d with
    | zero => intro _; exact ⟨by simpa using hz, fun i h1 h2 => by omega⟩
    | succ d ih =>
      intro hd
      obtain ⟨hst, hrows⟩ := ih (by omega)
      have hiR : i1 + d < R := by omega
      have hL2 := hlnI (i1 + d) (by omega) (by omega)
      obtain ⟨_, hrz, hout⟩ := row_fwd hL2 hf (hW _) (hint _ hiR) (hEL _ hiR) (hS _ hiR) hst
      refine ⟨?_, ?_⟩
      · have : st (i1 + (d + 1)) = st (i1 + d) + ln (i1 + d) := by
          rw [← Nat.add_assoc]; exact hstS _
        rw [this]; exact hout
      · intro i hi1 hi2 j hj
        by_cases heq : i = i1 + d
        · subst heq; exact hrz j hj
        · exact hrows i hi1 (by omega) j hj
  -- backward
  have hbwd : ∀ d : ℕ, d ≤ i1 - a → FSt e f (st (i1 - d)) ∧
      ∀ i, i1 - d ≤ i → i < i1 → ∀ j : ℕ, j < ln i → e (st i + j) = 0 := by
    intro d
    induction d with
    | zero => intro _; exact ⟨by simpa using hz, fun i h1 h2 => by omega⟩
    | succ d ih =>
      intro hd
      obtain ⟨hst, hrows⟩ := ih (by omega)
      have hiR : i1 - (d + 1) < R := by omega
      have hL2 := hlnI (i1 - (d + 1)) (by omega) (by omega)
      have hnext : st (i1 - (d + 1)) + ln (i1 - (d + 1)) = st (i1 - d) := by
        have := hstS (i1 - (d + 1))
        rw [show i1 - (d + 1) + 1 = i1 - d by omega] at this
        exact this.symm
      have hst' : FSt e f (st (i1 - (d + 1)) + ln (i1 - (d + 1))) := by rw [hnext]; exact hst
      obtain ⟨_, hrz, hin⟩ := row_bwd hL2 hf (hW _) (hint _ hiR) (hEL _ hiR) (hS _ hiR) hst'
      refine ⟨hin, ?_⟩
      intro i hi1 hi2 j hj
      by_cases heq : i = i1 - (d + 1)
      · subst heq; exact hrz j hj
      · exact hrows i (by omega) hi2 j hj
  intro i hi j hj
  by_cases hlt : i < a
  · have := hlnL i hlt
    have h0 : j = 0 := by omega
    subst h0
    simpa using hsingle i hi this
  by_cases hmid : i < i1
  · exact (hbwd (i1 - a) le_rfl).2 i (by omega) hmid j hj
  by_cases hfw : i < R - b
  · exact (hfwd (R - b - i1) (by omega)).2 i (by omega) (by omega) j hj
  · have hl1 := hlnR i (by omega) hi
    have h0 : j = 0 := by omega
    subst h0
    have hst := (hfwd (R - b - i1) (by omega)).1
    have e1 : st (i1 + (R - b - i1)) = st (R - b) := by rw [show i1 + (R - b - i1) = R - b by omega]
    rw [e1] at hst
    -- rows at and beyond `R - b` are singletons with zero value
    simpa using hsingle i hi hl1

end

end AdalyFormal.NcwdhTwo
