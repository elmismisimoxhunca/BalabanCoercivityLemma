import NuC4

/-!
# NuC5 -- the two-pair window lemma (lane ncwdh_ell2_20261018)

Four consecutive flat rows of the same length `L ≥ 2`, row multipliers `m 0, .., m 3`: `m 0 = m 1` and `m 2 = m 3` force the flux-zero state at the window start
(so by `uc_rows` the whole radical vector vanishes).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega

theorem pair_lemma {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {m : ℕ → ℝ} {s0 : ℤ}
    (hEL : ∀ k : ℕ, k ≤ 3 → BlockELs (s0 + (k : ℤ) * L) L e (m k))
    (hS : ∀ k : ℕ, k ≤ 3 → BlockSums (s0 + (k : ℤ) * L) L e)
    (h01 : m 0 = m 1) (h23 : m 2 = m 3) : StateZero e s0 := by
  have hrec := window_rec hL e m s0 3 hEL hS
  have r0 := hrec 0 (by norm_num)
  have r1 := hrec 1 (by norm_num)
  simp only [zero_add, Nat.reduceAdd] at r0 r1
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : 0 < (L : ℝ) ^ 2 - 1 := by nlinarith
  set τ : ℝ := (4 * (L : ℝ) ^ 2 + 2) / ((L : ℝ) ^ 2 - 1) with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have r0' : m 2 + m 0 = -τ * m 1 := by rw [hτ]; rw [neg_div] at r0; linarith
  have r1' : m 3 + m 1 = -τ * m 2 := by rw [hτ]; rw [neg_div] at r1; linarith
  have hab : m 0 = m 2 := by
    -- a + b = -τ a and a + b = -τ b
    have e1 : m 2 + m 0 = -τ * m 0 := by rw [r0', h01]
    have e2 : m 3 + m 1 = -τ * m 2 := r1'
    rw [← h23, ← h01] at e2
    have : τ * (m 0 - m 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hτpos.ne'
    · linarith
  have ha0 : m 0 = 0 := by
    have e1 : m 2 + m 0 = -τ * m 0 := by rw [r0', h01]
    rw [← hab] at e1
    have : (2 + τ) * m 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have ha1 : m 1 = 0 := by rw [← h01]; exact ha0
  have := fat_two_zero_s hL e m s0 1 le_rfl (fun k hk => hEL k (by omega)) (fun k hk => hS k (by omega)) 0 1 (by norm_num) le_rfl ha0 ha1
  have h0 := this.2 0 (Nat.zero_le _)
  simpa using h0

end AdalyFormal.NcwdhTwo
