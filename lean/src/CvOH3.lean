import CvOH2

/-!
# CvOH3 -- the three values of `omGe0` and the characterisation of `bondsLam` for direction-1 bonds (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

theorem omGe0_3 (v : ℕ) : ¬ omGe0 ell M R 3 v := by
  rintro ⟨i, h1, h2, -⟩
  omega

theorem omGe0_2 (hg : NGeo ell M R) (v : ℕ) : omGe0 ell M R 2 v ↔ reg2 ell M R v := by
  have hell := hg.hell
  have hpos : 0 < ell ^ 2 := by positivity
  constructor
  · rintro ⟨i, h1, h2, w, hd, hO, hN, hw1, hw2⟩
    have hi : i = 2 := by omega
    subst hi
    simp only [Omv] at hO
    unfold reg2 at hO ⊢
    rcases hO with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by omega, blk_lt hd hg.dB' b (by omega)⟩
    · right; exact ⟨by omega, blk_lt hd hg.dB b (by omega)⟩
  · intro h
    refine ⟨2, le_rfl, le_rfl, ell ^ 2 * (v / ell ^ 2), dvd_mul_right _ _, ?_, ?_, ?_, ?_⟩
    · simp only [Omv, reg2]
      unfold reg2 at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩
      · left
        have := down_blk hpos hg.dA' a (q := neB' ell M R)
        exact ⟨this.1, by have := this.2.2.1; omega⟩
      · right
        have := down_blk hpos hg.dA a (q := neB ell M R)
        exact ⟨this.1, by have := this.2.2.1; omega⟩
    · exact fun h => Omv_ge3 (by norm_num) _ h
    · exact Nat.mul_div_le v (ell ^ 2)
    · have := Nat.lt_mul_div_succ v hpos
      rw [mul_add, mul_one] at this
      exact this

theorem omGe0_mono {j j' v : ℕ} (h : j ≤ j') (hv : omGe0 ell M R j' v) : omGe0 ell M R j v := by
  obtain ⟨i, h1, h2, w, hw⟩ := hv
  exact ⟨i, by omega, h2, w, hw⟩

theorem omGe0_1 (hg : NGeo ell M R) (v : ℕ) : omGe0 ell M R 1 v ↔ (neP1 ell M R ≤ v ∧ v < neQ1 ell M R) := by
  have hell := hg.hell
  have hpos : 0 < ell := by omega
  have o1 := hg.hP0P1; have o2 := hg.hP1A; have o3 := hg.hAB'; have o4 := hg.hB'A; have o5 := hg.hAB; have o6 := hg.hBQ1
  constructor
  · rintro ⟨i, h1, h2, w, hd, hO, hN, hw1, hw2⟩
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · simp only [Omv] at hO
      refine ⟨by omega, blk_lt (by simpa using hd) hg.dQ1 hO.2 (by simpa using hw2)⟩
    · simp only [Omv] at hO
      unfold reg2 at hO
      rcases hO with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨by omega, by have := blk_lt hd hg.dB' b hw2; omega⟩
      · exact ⟨by omega, by have := blk_lt hd hg.dB b hw2; omega⟩
  · rintro ⟨a, b⟩
    by_cases h2 : reg2 ell M R v
    · exact omGe0_mono (by norm_num) ((omGe0_2 hg v).mpr h2)
    · have hb := down_blk hpos hg.dP1 a (q := neQ1 ell M R)
      refine ⟨1, le_rfl, by norm_num, ell * (v / ell), by simpa using dvd_mul_right ell (v / ell), ?_, ?_, ?_, ?_⟩
      · simp only [Omv]; exact ⟨hb.1, by have := hb.2.2.1; omega⟩
      · simp only [Omv]
        intro hr
        apply h2
        unfold reg2 at hr ⊢
        have hdw : ell ∣ ell * (v / ell) := dvd_mul_right _ _
        rcases hr with ⟨c, d⟩ | ⟨c, d⟩
        · left; exact ⟨by have := hb.2.2.1; omega, blk_lt hdw hg.dB'l d (by simpa using hb.2.2.2)⟩
        · right; exact ⟨by have := hb.2.2.1; omega, blk_lt hdw hg.dBl d (by simpa using hb.2.2.2)⟩
      · simpa using hb.2.2.1
      · simpa using hb.2.2.2

end AdalyFormal.CoverOmega
