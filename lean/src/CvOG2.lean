import CvOG1

/-!
# CvOG2 -- the row-start recursion tiles the nested tower (lane omega)

`isStart v`: `v` is the start of a row of some level.  `tile_step`: for a start `v` (with `v < Q0`): `v + rowLen v <= Q0`; it is either `Q0` or again a start; and the row never jumps
over `P1`, `Q1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem step_align (k a b : ℕ) (ha : k ∣ a) (hb : k ∣ b) (hab : a < b) : a + k ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hab
    · exact h
  have : x < y := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left k h
    omega
  have := Nat.mul_le_mul_left k (show x + 1 ≤ y from this)
  rw [mul_add, mul_one] at this
  exact this

/-- `v` starts a row. -/
def isStart (ell M R v : ℕ) : Prop := isRowN ell M R 0 v ∨ isRowN ell M R 1 v ∨ isRowN ell M R 2 v

theorem isStart_0 {w : ℕ} (h : isRowN ell M R 0 w) : isStart ell M R w := Or.inl h
theorem isStart_1 {w : ℕ} (h : isRowN ell M R 1 w) : isStart ell M R w := Or.inr (Or.inl h)
theorem isStart_2 {w : ℕ} (h : isRowN ell M R 2 w) : isStart ell M R w := Or.inr (Or.inr h)

theorem rowLen_0 (v : ℕ) (h : reg0 ell M R v) : rowLenN ell M R v = 1 := by
  unfold rowLenN; rw [if_pos h]

theorem rowLen_2 (v : ℕ) (h0 : ¬ reg0 ell M R v) (h2 : reg2 ell M R v) : rowLenN ell M R v = ell ^ 2 := by
  unfold rowLenN; rw [if_neg h0, if_pos h2]

theorem rowLen_1 (v : ℕ) (h0 : ¬ reg0 ell M R v) (h2 : ¬ reg2 ell M R v) : rowLenN ell M R v = ell := by
  unfold rowLenN; rw [if_neg h0, if_neg h2]

theorem reg0_not_reg2 (hg : NGeo ell M R) {v : ℕ} (h : reg0 ell M R v) : ¬ reg2 ell M R v := by
  obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _⟩ := hg
  unfold reg0 reg2 at *
  omega

theorem tile_step (hg : NGeo ell M R) {v : ℕ} (hv : isStart ell M R v) :
    v + rowLenN ell M R v ≤ neQ0 ell M R ∧
    (v + rowLenN ell M R v = neQ0 ell M R ∨ isStart ell M R (v + rowLenN ell M R v)) ∧
    (v < neP1 ell M R → v + rowLenN ell M R v ≤ neP1 ell M R) ∧
    (v < neQ1 ell M R → v + rowLenN ell M R v ≤ neQ1 ell M R) := by
  have hg' := hg
  obtain ⟨hell, hdell, o1, o2, o3, o4, o5, o6, o7, dP1, dQ1, dA', dB', dA, dB, dB'l, dAl, dBl, dA'l, cP, cQ, cRM⟩ := hg
  rcases hv with h | h | h
  · -- level 0
    have hr : rowLenN ell M R v = 1 := rowLen_0 v h
    rw [hr]
    simp only [isRowN, reg0] at h
    refine ⟨by omega, ?_, by omega, by omega⟩
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · by_cases hc : v + 1 < neP1 ell M R
      · exact Or.inr (isStart_0 (by simp only [isRowN, reg0]; omega))
      · have : v + 1 = neP1 ell M R := by omega
        rw [this]
        exact Or.inr (isStart_1 ⟨dP1, ⟨by omega, by omega⟩, by simp only [reg2]; omega⟩)
    · by_cases hc : v + 1 < neQ0 ell M R
      · exact Or.inr (isStart_0 (by simp only [isRowN, reg0]; omega))
      · exact Or.inl (by omega)
  · -- level 1
    simp only [isRowN, reg1] at h
    obtain ⟨hdv, ⟨hP, hQ⟩, hn2⟩ := h
    have hn0 : ¬ reg0 ell M R v := by
      unfold reg0; omega
    have hr : rowLenN ell M R v = ell := rowLen_1 v hn0 hn2
    rw [hr]
    unfold reg2 at hn2
    have hsQ : v + ell ≤ neQ1 ell M R := step_align ell v _ hdv dQ1 hQ
    have hsA' : v < neA' ell M R → v + ell ≤ neA' ell M R := fun h => step_align ell v _ hdv dA'l h
    have hsA : v < neA ell M R → v + ell ≤ neA ell M R := fun h => step_align ell v _ hdv dAl h
    refine ⟨by omega, ?_, by omega, fun _ => hsQ⟩
    by_cases hq : v + ell = neQ1 ell M R
    · rw [hq]; exact Or.inr (isStart_0 (by simp only [isRowN, reg0]; omega))
    · have hlt : v + ell < neQ1 ell M R := by omega
      by_cases h2 : reg2 ell M R (v + ell)
      · refine Or.inr (isStart_2 ⟨?_, h2⟩)
        unfold reg2 at h2
        rcases h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · have : v + ell = neA' ell M R := by
            by_cases hv' : v < neA' ell M R
            · have := hsA' hv'; omega
            · omega
          rw [this]; exact dA'
        · have : v + ell = neA ell M R := by
            by_cases hv' : v < neA ell M R
            · have := hsA hv'; omega
            · omega
          rw [this]; exact dA
      · exact Or.inr (isStart_1 ⟨dvd_add hdv dvd_rfl, ⟨by omega, hlt⟩, h2⟩)
  · -- level 2
    simp only [isRowN] at h
    obtain ⟨hdv, h2⟩ := h
    have hn0 : ¬ reg0 ell M R v := fun h0 => reg0_not_reg2 hg' h0 h2
    have hr : rowLenN ell M R v = ell ^ 2 := rowLen_2 v hn0 h2
    rw [hr]
    unfold reg2 at h2
    rcases h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · have hs : v + ell ^ 2 ≤ neB' ell M R := step_align _ v _ hdv dB' a2
      refine ⟨by omega, ?_, by omega, by omega⟩
      by_cases hq : v + ell ^ 2 = neB' ell M R
      · rw [hq]
        exact Or.inr (isStart_1 ⟨dB'l, ⟨by omega, by omega⟩, by simp only [reg2]; omega⟩)
      · exact Or.inr (isStart_2 ⟨dvd_add hdv dvd_rfl, by simp only [reg2]; left; omega⟩)
    · have hs : v + ell ^ 2 ≤ neB ell M R := step_align _ v _ hdv dB a2
      refine ⟨by omega, ?_, by omega, by omega⟩
      by_cases hq : v + ell ^ 2 = neB ell M R
      · rw [hq]
        exact Or.inr (isStart_1 ⟨dBl, ⟨by omega, by omega⟩, by simp only [reg2]; omega⟩)
      · exact Or.inr (isStart_2 ⟨dvd_add hdv dvd_rfl, by simp only [reg2]; right; omega⟩)

#print axioms tile_step

end AdalyFormal.CoverOmega
