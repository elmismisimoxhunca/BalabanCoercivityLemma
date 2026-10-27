import NsOdd5b

/-!
# NsOdd6a -- the real-number inequalities behind the level-1 loop bound for ODD `ell` (lane ncwdh_strong_20261017)

`W₀, W₁, W₂` are the normalised loop angles (loop = `t (-1)^{y₁} W`) of `phi1o` in the three directions, with the T-part, the `D`-part (amplitude
`a ∈ [0, A]`, `2A ≤ 1`) and the `E`-part (alternating sums `e_i` of the amplitude `p`, `|e_i| ≤ ε`, `|E| ≤ Em`) separated.
Each is bounded by `1 + 3 Em ε`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false

/-- direction 1. -/
theorem loop1_real (T0 Tx Dsum E0 Ex e1 e2 e3 e4 a1 a2 pm1 n1odd A Em ε : ℝ)
    (hT0 : T0 = 0 ∨ T0 = 1) (hTx : Tx = 0 ∨ Tx = 1) (hD : Dsum = T0 - Tx)
    (hpm : (pm1 = 1 ∧ n1odd = 0) ∨ (pm1 = -1 ∧ n1odd = 1))
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ A) (hA : 2 * A ≤ 1)
    (hE0 : |E0| ≤ Em) (hEx : |Ex| ≤ Em) (he1 : |e1| ≤ ε) (he2 : |e2| ≤ ε) (he3 : |e3| ≤ ε) (he4 : |e4| ≤ ε)
    (hz1 : T0 = 1 → Tx = 0 → Ex = 0) (hz2 : T0 = 0 → Tx = 1 → E0 = 0)
    (hEm : 0 ≤ Em) (hε : 0 ≤ ε) (hEε : Em * ε ≤ 1) :
    |(2 * n1odd * T0 + pm1 * Tx - T0 + pm1 * Dsum * (a1 + a2)) + (E0 * (e1 + e2 - e4) + pm1 * Ex * e3)| ≤ 1 + 3 * Em * ε := by
  have hb : ∀ (E e : ℝ), |E| ≤ Em → |e| ≤ ε → -(Em * ε) ≤ E * e ∧ E * e ≤ Em * ε := fun E e hE he => by
    have : |E * e| ≤ Em * ε := by rw [abs_mul]; exact mul_le_mul hE he (abs_nonneg _) hEm
    exact abs_le.mp this
  obtain ⟨b1l, b1u⟩ := hb E0 e1 hE0 he1
  obtain ⟨b2l, b2u⟩ := hb E0 e2 hE0 he2
  obtain ⟨b4l, b4u⟩ := hb E0 e4 hE0 he4
  obtain ⟨b3l, b3u⟩ := hb Ex e3 hEx he3
  have key : (2 * n1odd * T0 + pm1 * Tx - T0 + pm1 * Dsum * (a1 + a2)) + (E0 * (e1 + e2 - e4) + pm1 * Ex * e3) =
      (2 * n1odd * T0 + pm1 * Tx - T0 + pm1 * Dsum * (a1 + a2)) + ((E0 * e1) + (E0 * e2) - (E0 * e4) + pm1 * (Ex * e3)) := by ring
  rw [key, hD]
  rcases hT0 with h0 | h0 <;> rcases hTx with hx | hx <;> rcases hpm with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;> subst h0 hx hp hn
  · -- (0,0), even
    rw [abs_le]; constructor <;> nlinarith
  · -- (0,0), odd
    rw [abs_le]; constructor <;> nlinarith
  · -- (0,1), even
    have : E0 = 0 := hz2 rfl rfl
    subst this
    rw [abs_le]; constructor <;> nlinarith
  · -- (0,1), odd
    have : E0 = 0 := hz2 rfl rfl
    subst this
    rw [abs_le]; constructor <;> nlinarith
  · -- (1,0), even
    have : Ex = 0 := hz1 rfl rfl
    subst this
    rw [abs_le]; constructor <;> nlinarith
  · -- (1,0), odd
    have : Ex = 0 := hz1 rfl rfl
    subst this
    rw [abs_le]; constructor <;> nlinarith
  · -- (1,1), even
    rw [abs_le]; constructor <;> nlinarith
  · -- (1,1), odd
    rw [abs_le]; constructor <;> nlinarith

/-- direction 0. -/
theorem loop0_real (X Ed e1 a1 ay pm1 n1odd A Em ε : ℝ)
    (hX : X = -1 ∨ X = 0 ∨ X = 1) (hpm : (pm1 = 1 ∧ n1odd = 0) ∨ (pm1 = -1 ∧ n1odd = 1))
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (hay : 0 ≤ ay) (hay' : ay ≤ A) (hA : 2 * A ≤ 1)
    (hEd : |Ed| ≤ Em) (he1 : |e1| ≤ ε) (hEm : 0 ≤ Em) (hε : 0 ≤ ε) :
    |n1odd * X + Ed * e1 + X * (pm1 * a1 - ay)| ≤ 1 + 3 * Em * ε := by
  have hb : -(Em * ε) ≤ Ed * e1 ∧ Ed * e1 ≤ Em * ε := by
    have : |Ed * e1| ≤ Em * ε := by rw [abs_mul]; exact mul_le_mul hEd he1 (abs_nonneg _) hEm
    exact abs_le.mp this
  have hm0 : 0 ≤ Em * ε := mul_nonneg hEm hε
  obtain ⟨bl, bu⟩ := hb
  rcases hX with h | h | h <;> rcases hpm with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;> subst h hp hn <;> (rw [abs_le]; constructor <;> nlinarith)

/-- direction 2. -/
theorem loop2_real (Dsum E0 e1 e2 a1 a2 pm1 A Em ε : ℝ)
    (hD : Dsum = -1 ∨ Dsum = 0 ∨ Dsum = 1) (hpm : pm1 = 1 ∨ pm1 = -1)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ A) (hA : 2 * A ≤ 1)
    (hE0 : |E0| ≤ Em) (he1 : |e1| ≤ ε) (he2 : |e2| ≤ ε) (hEm : 0 ≤ Em) (hε : 0 ≤ ε) :
    |E0 * (e1 - e2) + pm1 * Dsum * (a1 - a2)| ≤ 1 + 3 * Em * ε := by
  have hb : ∀ e : ℝ, |e| ≤ ε → -(Em * ε) ≤ E0 * e ∧ E0 * e ≤ Em * ε := fun e he => by
    have : |E0 * e| ≤ Em * ε := by rw [abs_mul]; exact mul_le_mul hE0 he (abs_nonneg _) hEm
    exact abs_le.mp this
  obtain ⟨b1l, b1u⟩ := hb e1 he1
  obtain ⟨b2l, b2u⟩ := hb e2 he2
  have hm0 : 0 ≤ Em * ε := mul_nonneg hEm hε
  have key : E0 * (e1 - e2) + pm1 * Dsum * (a1 - a2) = (E0 * e1) - (E0 * e2) + pm1 * Dsum * (a1 - a2) := by ring
  rw [key]
  rcases hD with h | h | h <;> rcases hpm with hp | hp <;> subst h hp <;> (rw [abs_le]; constructor <;> nlinarith)

end AdalyFormal.CoverOmega
