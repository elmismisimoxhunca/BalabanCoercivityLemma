import NtOdd5b

/-!
# NsOdd6a -- the real-number inequalities behind the level-1 loop bound for ODD `ell` (lane ncwdh_strong_20261017)

`W₀, W₁, W₂` are the normalised loop angles (loop = `t (-1)^{y₁} W`) of `phi1o` in the three directions, with the T-part, the `D`-part (amplitude
`a ∈ [0, A]`, `2A ≤ 1`) and the `E`-part (alternating sums `e_i` of the amplitude `p`, `|e_i| ≤ ε`, `|E| ≤ Em`) separated.
Each is bounded by `1 + 3 Em ε` (`loop1_real`, `loop0_real`, `loop2_real`; SUPERSEDED in this fork by the `*_real2` versions below with bound `1 + 2 Em ε`; the old three are no longer used).
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


/-! ## refined (parity-range) versions, bound `1 + 2 Em ε` with `ε = 2u` (valid for `ell ≥ 3`, i.e. `Em ≥ 2`) -/

theorem prod_both (E e lo hi Em : ℝ) (hEm : 0 ≤ Em) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (h1 : lo ≤ e) (h2 : e ≤ hi) :
    (E = -Em → -(Em * hi) ≤ E * e ∧ E * e ≤ -(Em * lo)) ∧ (0 ≤ E → E ≤ 1 → lo ≤ E * e ∧ E * e ≤ hi) := by
  constructor
  · intro hE
    subst hE
    constructor <;> nlinarith [mul_nonneg hEm (sub_nonneg.2 h1), mul_nonneg hEm (sub_nonneg.2 h2)]
  · intro hE0 hE1
    constructor <;> nlinarith [mul_nonneg hE0 (sub_nonneg.2 h2), mul_nonneg hE0 (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 h2)]

theorem loop1_real2 (T0 Tx Dsum E0 Ex e1 e2 e3 e4 a1 a2 pm1 n1odd A Em u : ℝ)
    (hT0 : T0 = 0 ∨ T0 = 1) (hTx : Tx = 0 ∨ Tx = 1) (hD : Dsum = T0 - Tx)
    (hpm : (pm1 = 1 ∧ n1odd = 0) ∨ (pm1 = -1 ∧ n1odd = 1))
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ A) (hA : 2 * A ≤ 1)
    (hE0 : (T0 = 1 → E0 = -Em) ∧ (T0 = 0 → 0 ≤ E0 ∧ E0 ≤ 1))
    (hEx : (Tx = 1 → Ex = -Em) ∧ (Tx = 0 → 0 ≤ Ex ∧ Ex ≤ 1))
    (he12o : n1odd = 1 → 0 ≤ e1 ∧ e1 ≤ 2 * u ∧ 0 ≤ e2 ∧ e2 ≤ 2 * u)
    (he12e : n1odd = 0 → -u ≤ e1 ∧ e1 ≤ u ∧ -u ≤ e2 ∧ e2 ≤ u)
    (he3 : 0 ≤ e3 ∧ e3 ≤ 2 * u) (he4 : 0 ≤ e4 ∧ e4 ≤ 2 * u)
    (hz1 : T0 = 1 → Tx = 0 → Ex = 0) (hz2 : T0 = 0 → Tx = 1 → E0 = 0)
    (hEm : 2 ≤ Em) (hu : 0 ≤ u) :
    |(2 * n1odd * T0 + pm1 * Tx - T0 + pm1 * Dsum * (a1 + a2)) + (E0 * (e1 + e2 - e4) + pm1 * Ex * e3)| ≤ 1 + 2 * Em * (2 * u) := by
  have hEm0 : 0 ≤ Em := by linarith
  obtain ⟨he3l, he3u⟩ := he3
  obtain ⟨he4l, he4u⟩ := he4
  have hEu : 0 ≤ Em * u := mul_nonneg hEm0 hu
  have hEu2 : 2 * u ≤ Em * u := by nlinarith
  rw [hD]
  rcases hpm with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · subst hp hn
    obtain ⟨h1l, h1u, h2l, h2u⟩ := he12e rfl
    have f1 := prod_both E0 e1 (-u) u Em hEm0 (by linarith) hu h1l h1u
    have f2 := prod_both E0 e2 (-u) u Em hEm0 (by linarith) hu h2l h2u
    have f4 := prod_both E0 e4 0 (2 * u) Em hEm0 le_rfl (by linarith) he4l he4u
    have f3 := prod_both Ex e3 0 (2 * u) Em hEm0 le_rfl (by linarith) he3l he3u
    rcases hT0 with h0 | h0 <;> rcases hTx with hx | hx <;> subst h0 hx
    · obtain ⟨g0l, g0u⟩ := hE0.2 rfl
      obtain ⟨gxl, gxu⟩ := hEx.2 rfl
      have a1' := f1.2 g0l g0u; have a2' := f2.2 g0l g0u; have a4' := f4.2 g0l g0u; have a3' := f3.2 gxl gxu
      rw [abs_le]; constructor <;> nlinarith
    · have g0 := hz2 rfl rfl
      have gx := hEx.1 rfl
      have a3' := f3.1 gx
      subst g0
      rw [abs_le]; constructor <;> nlinarith
    · have gx := hz1 rfl rfl
      have g0 := hE0.1 rfl
      have a1' := f1.1 g0; have a2' := f2.1 g0; have a4' := f4.1 g0
      subst gx
      rw [abs_le]; constructor <;> nlinarith
    · have g0 := hE0.1 rfl
      have gx := hEx.1 rfl
      have a1' := f1.1 g0; have a2' := f2.1 g0; have a4' := f4.1 g0; have a3' := f3.1 gx
      rw [abs_le]; constructor <;> nlinarith
  · subst hp hn
    obtain ⟨h1l, h1u, h2l, h2u⟩ := he12o rfl
    have f1 := prod_both E0 e1 0 (2 * u) Em hEm0 le_rfl (by linarith) h1l h1u
    have f2 := prod_both E0 e2 0 (2 * u) Em hEm0 le_rfl (by linarith) h2l h2u
    have f4 := prod_both E0 e4 0 (2 * u) Em hEm0 le_rfl (by linarith) he4l he4u
    have f3 := prod_both Ex e3 0 (2 * u) Em hEm0 le_rfl (by linarith) he3l he3u
    rcases hT0 with h0 | h0 <;> rcases hTx with hx | hx <;> subst h0 hx
    · obtain ⟨g0l, g0u⟩ := hE0.2 rfl
      obtain ⟨gxl, gxu⟩ := hEx.2 rfl
      have a1' := f1.2 g0l g0u; have a2' := f2.2 g0l g0u; have a4' := f4.2 g0l g0u; have a3' := f3.2 gxl gxu
      rw [abs_le]; constructor <;> nlinarith
    · have g0 := hz2 rfl rfl
      have gx := hEx.1 rfl
      have a3' := f3.1 gx
      subst g0
      rw [abs_le]; constructor <;> nlinarith
    · have gx := hz1 rfl rfl
      have g0 := hE0.1 rfl
      have a1' := f1.1 g0; have a2' := f2.1 g0; have a4' := f4.1 g0
      subst gx
      rw [abs_le]; constructor <;> nlinarith
    · have g0 := hE0.1 rfl
      have gx := hEx.1 rfl
      have a1' := f1.1 g0; have a2' := f2.1 g0; have a4' := f4.1 g0; have a3' := f3.1 gx
      rw [abs_le]; constructor <;> nlinarith


/-- direction 0, refined bound `1 + 2 Em ε`. -/
theorem loop0_real2 (X Ed e1 a1 ay pm1 n1odd A Em ε : ℝ)
    (hX : X = -1 ∨ X = 0 ∨ X = 1) (hpm : (pm1 = 1 ∧ n1odd = 0) ∨ (pm1 = -1 ∧ n1odd = 1))
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (hay : 0 ≤ ay) (hay' : ay ≤ A) (hA : 2 * A ≤ 1)
    (hEd : |Ed| ≤ Em) (he1 : |e1| ≤ ε) (hEm : 0 ≤ Em) (hε : 0 ≤ ε) :
    |n1odd * X + Ed * e1 + X * (pm1 * a1 - ay)| ≤ 1 + 2 * Em * ε := by
  have hb : -(Em * ε) ≤ Ed * e1 ∧ Ed * e1 ≤ Em * ε := by
    have : |Ed * e1| ≤ Em * ε := by rw [abs_mul]; exact mul_le_mul hEd he1 (abs_nonneg _) hEm
    exact abs_le.mp this
  have hm0 : 0 ≤ Em * ε := mul_nonneg hEm hε
  obtain ⟨bl, bu⟩ := hb
  rcases hX with h | h | h <;> rcases hpm with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;> subst h hp hn <;> (rw [abs_le]; constructor <;> nlinarith)

/-- direction 2, refined bound `1 + 2 Em ε`. -/
theorem loop2_real2 (Dsum E0 e1 e2 a1 a2 pm1 A Em ε : ℝ)
    (hD : Dsum = -1 ∨ Dsum = 0 ∨ Dsum = 1) (hpm : pm1 = 1 ∨ pm1 = -1)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ A) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ A) (hA : 2 * A ≤ 1)
    (hE0 : |E0| ≤ Em) (he1 : |e1| ≤ ε) (he2 : |e2| ≤ ε) (hEm : 0 ≤ Em) (hε : 0 ≤ ε) :
    |E0 * (e1 - e2) + pm1 * Dsum * (a1 - a2)| ≤ 1 + 2 * Em * ε := by
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
