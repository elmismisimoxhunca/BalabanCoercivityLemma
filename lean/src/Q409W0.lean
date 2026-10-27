import P409D
import GenCl1

/-!
# Q409W0 -- arithmetic on circular distances and block indices (no tower content).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409W

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

/-- `(a+s) mod N` is `a+s` or `a+s-N`. -/
theorem mod_add_cases (a s N : ℕ) (ha : a < N) (hs : s ≤ N) :
    (a + s < N ∧ (a + s) % N = a + s) ∨ (N ≤ a + s ∧ (a + s) % N = a + s - N) := by
  by_cases h : a + s < N
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    refine ⟨by omega, ?_⟩
    have h1 : (a + s) % N = (a + s - N) % N := Nat.mod_eq_sub_mod (by omega)
    rw [h1]
    exact Nat.mod_eq_of_lt (by omega)

theorem pcd_shift_le (N a s : ℕ) (ha : a < N) (hs : s ≤ N) :
    pcd N a ((a + s) % N) ≤ s ∧ pcd N a ((a + s) % N) ≤ N - s := by
  rcases mod_add_cases a s N ha hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> unfold pcd <;> split_ifs <;> omega

theorem blocks_ne (g N a s : ℕ) (hg : 0 < g) (hgN : g ∣ N) (hgs : g ∣ s) (hs0 : 0 < s) (hsN : s < N)
    (ha : a < N) : ((a + s) % N) / g ≠ a / g := by
  obtain ⟨N', rfl⟩ := hgN
  obtain ⟨s', rfl⟩ := hgs
  rcases mod_add_cases a (g * s') (g * N') ha hsN.le with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, Nat.add_mul_div_left a s' hg]
    have : 0 < s' := by
      rcases Nat.eq_zero_or_pos s' with h | h
      · subst h; simp at hs0
      · exact h
    omega
  · have hb : (a + g * s' - g * N') + g * N' = a + g * s' := by omega
    have h3 : ((a + g * s' - g * N') + g * N') / g = (a + g * s' - g * N') / g + N' := by
      rw [Nat.add_comm (a + g * s' - g * N'), Nat.mul_add_div hg N']
      omega
    rw [hb, Nat.add_mul_div_left a s' hg] at h3
    rw [h2]
    have : s' < N' := by
      by_contra hh
      push Not at hh
      have := Nat.mul_le_mul_left g hh
      omega
    omega

theorem div_shift (M N a a' s : ℕ) (hM : 0 < M) (hMN : M ∣ N) (hMs : M ∣ s) (h : a / M = a' / M) :
    ((a + s) % N) / M = ((a' + s) % N) / M := by
  obtain ⟨N', rfl⟩ := hMN
  obtain ⟨s', rfl⟩ := hMs
  have key : ∀ b : ℕ, ((b + M * s') % (M * N')) / M = (b / M + s') % N' := by
    intro b
    rw [Nat.mod_mul_right_div_self, Nat.add_mul_div_left b s' hM]
  rw [key, key, h]

/-- `a'` is one `M`-step from `a`, toward `b`: it decreases the circular distance by `M` when that is at least `M`,
and is within `M` otherwise. -/
theorem pcd_toward (N M a b : ℕ) (hM : 0 < M) (h2 : 2 * M ≤ N) (ha : a < N) (hb : b < N) :
    ∃ s : ℕ, (s = M ∨ s + M = N) ∧
      ((M ≤ pcd N a b → pcd N ((a + s) % N) b + M ≤ pcd N a b) ∧
       (pcd N a b < M → pcd N ((a + s) % N) b ≤ M)) := by
  have hc1 := mod_add_cases a M N ha (by omega)
  have hc2 := mod_add_cases a (N - M) N ha (by omega)
  by_cases hf : (if a ≤ b then b - a else b + N - a) ≤ N - (if a ≤ b then b - a else b + N - a)
  · refine ⟨M, Or.inl rfl, ?_⟩
    rcases hc1 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> rw [h3] <;> unfold pcd <;> split_ifs at hf ⊢ <;> omega
  · refine ⟨N - M, Or.inr (by omega), ?_⟩
    rcases hc2 with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> rw [h3] <;> unfold pcd <;> split_ifs at hf ⊢ <;> omega

end AdalyFormal.P409W
