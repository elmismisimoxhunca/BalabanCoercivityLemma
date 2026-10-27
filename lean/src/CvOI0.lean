import CvOH5

/-!
# CvOI0 -- every slice of `[P0,Q0)` lies in exactly one row: `levN`, `rstartN`, `row_unique` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

variable {ell M R : ℕ}

open Classical in
/-- the level of the row containing slice `v`. -/
noncomputable def levN (ell M R v : ℕ) : ℕ := if reg0 ell M R v then 0 else if reg2 ell M R v then 2 else 1

/-- the start of the row containing slice `v`. -/
noncomputable def rstartN (ell M R v : ℕ) : ℕ := ell ^ levN ell M R v * (v / ell ^ levN ell M R v)

theorem levN_0 {v : ℕ} (h : reg0 ell M R v) : levN ell M R v = 0 := by unfold levN; rw [if_pos h]
theorem levN_2 {v : ℕ} (h0 : ¬ reg0 ell M R v) (h2 : reg2 ell M R v) : levN ell M R v = 2 := by unfold levN; rw [if_neg h0, if_pos h2]
theorem levN_1 {v : ℕ} (h0 : ¬ reg0 ell M R v) (h2 : ¬ reg2 ell M R v) : levN ell M R v = 1 := by unfold levN; rw [if_neg h0, if_neg h2]

theorem reg0_or (hg : NGeo ell M R) {v : ℕ} (hv : neP0 ell M R ≤ v ∧ v < neQ0 ell M R) :
    reg0 ell M R v ∨ reg1 ell M R v ∨ reg2 ell M R v := by
  have := hg.hP0P1; have := hg.hP1A; have := hg.hAB'; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1; have := hg.hQ1Q0
  unfold reg0 reg1 reg2 at *
  by_cases h2 : (neA' ell M R ≤ v ∧ v < neB' ell M R) ∨ (neA ell M R ≤ v ∧ v < neB ell M R)
  · right; right; exact h2
  · by_cases h1 : neP1 ell M R ≤ v ∧ v < neQ1 ell M R
    · right; left; exact ⟨h1, h2⟩
    · left; omega

theorem row_unique (hg : NGeo ell M R) {v : ℕ} (hv : neP0 ell M R ≤ v ∧ v < neQ0 ell M R) {j : ℕ} (hj : j ≤ 2) :
    isRowN ell M R j (ell ^ j * (v / ell ^ j)) ↔ j = levN ell M R v := by
  have hell := hg.hell
  have hpos1 : 0 < ell := by omega
  have hpos2 : 0 < ell ^ 2 := by positivity
  have hℓ2 : ell ∣ ell ^ 2 := dvd_pow_self ell (by norm_num)
  have o1 := hg.hP0P1; have o2 := hg.hP1A; have o3 := hg.hAB'; have o4 := hg.hB'A; have o5 := hg.hAB; have o6 := hg.hBQ1; have o7 := hg.hQ1Q0
  have hb1 := fun (p : ℕ) (hp : ell ∣ p) (hpv : p ≤ v) => down_blk (q := 0) hpos1 hp hpv
  have hb2 := fun (p : ℕ) (hp : ell ^ 2 ∣ p) (hpv : p ≤ v) => down_blk (q := 0) hpos2 hp hpv
  have hdw1 : ell ∣ ell * (v / ell) := dvd_mul_right _ _
  have hdw2 : ell ^ 2 ∣ ell ^ 2 * (v / ell ^ 2) := dvd_mul_right _ _
  have hle1 := Nat.mul_div_le v ell
  have hle2 := Nat.mul_div_le v (ell ^ 2)
  have hlt1 : v < ell * (v / ell) + ell := by
    have := Nat.lt_mul_div_succ v hpos1; rw [mul_add, mul_one] at this; exact this
  have hlt2 : v < ell ^ 2 * (v / ell ^ 2) + ell ^ 2 := by
    have := Nat.lt_mul_div_succ v hpos2; rw [mul_add, mul_one] at this; exact this
  rcases reg0_or hg hv with h0 | h1 | h2
  · have hl : levN ell M R v = 0 := levN_0 h0
    rw [hl]
    unfold reg0 at h0
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simp only [pow_zero, Nat.div_one, one_mul, isRowN]; exact ⟨fun _ => trivial, fun _ => by unfold reg0; exact h0⟩
    · simp only [pow_one, isRowN, reg1]
      constructor
      · rintro ⟨_, ⟨a1, a2⟩, _⟩
        rcases h0 with ⟨c, d⟩ | ⟨c, d⟩
        · omega
        · have := (hb1 _ hg.dQ1 c).1; omega
      · intro h; omega
    · simp only [isRowN, reg2]
      constructor
      · rintro ⟨_, h⟩
        rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · rcases h0 with ⟨c, d⟩ | ⟨c, d⟩
          · omega
          · have := blk_lt hdw2 hg.dB' a2 hlt2; omega
        · have := blk_lt hdw2 hg.dB a2 hlt2
          rcases h0 with ⟨c, d⟩ | ⟨c, d⟩ <;> omega
      · intro h; omega
  · have hn0 : ¬ reg0 ell M R v := by unfold reg0 reg1 at *; omega
    have hl : levN ell M R v = 1 := levN_1 hn0 h1.2
    rw [hl]
    obtain ⟨⟨c1, c2⟩, hn2⟩ := h1
    unfold reg2 at hn2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simp only [pow_zero, Nat.div_one, one_mul, isRowN, reg0]
      constructor
      · intro h; omega
      · intro h; omega
    · simp only [pow_one, isRowN, reg1]
      refine ⟨fun _ => trivial, fun _ => ⟨hdw1, ⟨?_, ?_⟩, ?_⟩⟩
      · exact (hb1 _ hg.dP1 c1).1
      · omega
      · unfold reg2
        rintro (⟨a1, a2⟩ | ⟨a1, a2⟩)
        · have := blk_lt hdw1 hg.dB'l a2 hlt1; omega
        · have := blk_lt hdw1 hg.dBl a2 hlt1; omega
    · simp only [isRowN, reg2]
      constructor
      · rintro ⟨_, h⟩
        rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · have := blk_lt hdw2 hg.dB' a2 hlt2; omega
        · have := blk_lt hdw2 hg.dB a2 hlt2; omega
      · intro h; omega
  · have hn0 : ¬ reg0 ell M R v := fun h => reg0_not_reg2 hg h h2
    have hl : levN ell M R v = 2 := levN_2 hn0 h2
    rw [hl]
    unfold reg2 at h2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simp only [pow_zero, Nat.div_one, one_mul, isRowN]
      constructor
      · intro h; exact absurd h hn0
      · intro h; omega
    · simp only [pow_one, isRowN, reg1]
      constructor
      · rintro ⟨_, _, hn2⟩
        exfalso
        apply hn2
        unfold reg2
        rcases h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · left; exact ⟨by have := (hb1 _ hg.dA'l a1).1; omega, by omega⟩
        · right; exact ⟨by have := (hb1 _ hg.dAl a1).1; omega, by omega⟩
      · intro h; omega
    · simp only [isRowN, reg2]
      refine ⟨fun _ => trivial, fun _ => ⟨hdw2, ?_⟩⟩
      rcases h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · left; exact ⟨(hb2 _ hg.dA' a1).1, by omega⟩
      · right; exact ⟨(hb2 _ hg.dA a1).1, by omega⟩

#print axioms row_unique

end AdalyFormal.CoverOmega
