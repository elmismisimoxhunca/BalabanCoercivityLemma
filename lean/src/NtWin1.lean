import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# NtWin1 -- two-window lemma for a three-term recurrence (lane ncwdh_small_ell_20261018)

For `tau > 2` and a real sequence `mu` obeying `mu (k+2) + mu k = -tau * mu (k+1)` for `k + 2 <= ell + 1`:
if `mu 0 = mu 1` and `mu ell = mu (ell + 1)` (`1 <= ell`) then `mu 0 = 0` and `mu 1 = 0`.
So at least one of the two windows `(0,1)`, `(ell, ell+1)` has `mu` taking different values.
-/
set_option autoImplicit false

namespace AdalyFormal.CoverOmega.Win

/-- the sign-normalised solution `t_0 = -1, t_1 = 1, t_{k+2} = tau t_{k+1} - t_k`. -/
noncomputable def tSeq (τ : ℝ) : ℕ → ℝ
  | 0 => -1
  | 1 => 1
  | (k + 2) => τ * tSeq τ (k + 1) - tSeq τ k

theorem tSeq_mono (τ : ℝ) (hτ : 2 < τ) : ∀ k : ℕ, 0 < tSeq τ (k + 1) ∧ tSeq τ (k + 1) ≤ tSeq τ (k + 2) := by
  intro k
  induction k with
  | zero => simp [tSeq]; linarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : tSeq τ (k + 1 + 2) = τ * tSeq τ (k + 2) - tSeq τ (k + 1) := rfl
    constructor
    · linarith
    · rw [e]; nlinarith

theorem tSeq_pos (τ : ℝ) (hτ : 2 < τ) {k : ℕ} (hk : 1 ≤ k) : 0 < tSeq τ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (tSeq_mono τ hτ j).1

theorem seq_pair_ne (τ : ℝ) (hτ : 2 < τ) (mu : ℕ → ℝ) (ell : ℕ) (hell : 1 ≤ ell)
    (hrec : ∀ k, k + 2 ≤ ell + 1 → mu (k + 2) + mu k = -τ * mu (k + 1))
    (h0 : mu 0 = mu 1) (hl : mu ell = mu (ell + 1)) : mu 0 = 0 ∧ mu 1 = 0 := by
  set T : ℕ → ℝ := fun k => (-1) ^ (k + 1) * mu k with hT
  have hTrec : ∀ k, k + 2 ≤ ell + 1 → T (k + 2) = τ * T (k + 1) - T k := by
    intro k hk
    have := hrec k hk
    simp only [hT]
    have e1 : ((-1 : ℝ)) ^ (k + 2 + 1) = (-1) ^ (k + 1) := by ring
    have e2 : ((-1 : ℝ)) ^ (k + 1 + 1) = -(-1) ^ (k + 1) := by ring
    rw [e1, e2]
    have : mu (k + 2) = -τ * mu (k + 1) - mu k := by linarith
    rw [this]; ring
  have hT01 : T 0 = -mu 1 := by simp only [hT]; rw [← h0]; ring
  have hT1 : T 1 = mu 1 := by simp only [hT]; norm_num
  have hgen : ∀ k, k + 1 ≤ ell + 1 → T k = mu 1 * tSeq τ k ∧ T (k + 1) = mu 1 * tSeq τ (k + 1) := by
    intro k
    induction k with
    | zero => intro _; refine ⟨?_, ?_⟩ <;> simp [tSeq, hT01, hT1]
    | succ k ih =>
      intro hk
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨b, ?_⟩
      have e : tSeq τ (k + 1 + 1) = τ * tSeq τ (k + 1) - tSeq τ k := rfl
      rw [e, mul_sub, ← mul_assoc, mul_comm (mu 1) τ, mul_assoc, ← b, ← a]
      exact hTrec k hk
  obtain ⟨-, hell1⟩ := hgen ell (by omega)
  obtain ⟨hell0, -⟩ := hgen ell (by omega)
  have hTl : T (ell + 1) = -T ell := by
    simp only [hT]
    have : ((-1 : ℝ)) ^ (ell + 1 + 1) = -(-1) ^ (ell + 1) := by ring
    rw [this, ← hl]; ring
  have hp1 := tSeq_pos τ hτ hell
  have hp2 := tSeq_pos τ hτ (show 1 ≤ ell + 1 by omega)
  have hb : mu 1 * (tSeq τ ell + tSeq τ (ell + 1)) = 0 := by
    rw [mul_add, ← hell0, ← hell1, hTl]; ring
  have hsum : tSeq τ ell + tSeq τ (ell + 1) ≠ 0 := by linarith
  have hm1 : mu 1 = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact absurd h hsum
  exact ⟨by rw [h0, hm1], hm1⟩

#print axioms seq_pair_ne

end AdalyFormal.CoverOmega.Win
