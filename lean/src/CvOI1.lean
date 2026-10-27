import CvOI0

/-!
# CvOI1 -- the chain row containing a slice is the row `(levN v, rstartN v)` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem isRowN_dvd {j v : ℕ} (h : isRowN ell M R j v) : ell ^ j ∣ v ∧ j ≤ 2 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj
  · exact ⟨by simp, by norm_num⟩
  · exact ⟨by simpa using h.1, by norm_num⟩
  · exact ⟨h.1, le_rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
    simp [isRowN] at h

theorem rowLen_of_isRowN (hg : NGeo ell M R) {j v : ℕ} (h : isRowN ell M R j v) : rowLenN ell M R v = ell ^ j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj
  · simp only [isRowN] at h; simpa using rowLen_0 v h
  · simp only [isRowN, reg1] at h
    obtain ⟨_, ⟨a, b⟩, hn2⟩ := h
    have hn0 : ¬ reg0 ell M R v := by unfold reg0; have := hg.hP0P1; have := hg.hQ1Q0; omega
    simpa using rowLen_1 v hn0 hn2
  · simp only [isRowN] at h
    exact rowLen_2 v (fun h0 => reg0_not_reg2 hg h0 h.2) h.2
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
    simp [isRowN] at h

theorem chain_row_level (hg : NGeo ell M R) {x : ℕ} (hx : x < nN ell M R) :
    neP0 ell M R + stN ell M R (rowOfN ell M R x) = rstartN ell M R (neP0 ell M R + x) ∧
    lnN ell M R (rowOfN ell M R x) = ell ^ levN ell M R (neP0 ell M R + x) := by
  obtain ⟨hiR, hs1, hs2⟩ := rowOfN_spec hg hx
  set i := rowOfN ell M R x with hi
  have hstart := RN_start hg i hiR
  have hI : neP0 ell M R ≤ neP0 ell M R + x ∧ neP0 ell M R + x < neQ0 ell M R := by
    unfold nN at hx
    have := hg.hP0P1; have := hg.hQ1Q0; have := hg.hP1A; have := hg.hAB'; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1
    omega
  rcases hstart with h | h | h
  · have hln : lnN ell M R i = 1 := by have := rowLen_of_isRowN hg h; unfold lnN; simpa using this
    have hx_eq : x = stN ell M R i := by rw [stN_succ, hln] at hs2; omega
    have hlev : 0 = levN ell M R (neP0 ell M R + x) := by
      rw [← row_unique hg hI (show 0 ≤ 2 by norm_num)]
      simp only [pow_zero, Nat.div_one, one_mul]
      rw [hx_eq]; exact h
    refine ⟨?_, ?_⟩
    · unfold rstartN; rw [← hlev]; simp only [pow_zero, Nat.div_one, one_mul]; omega
    · rw [← hlev]; simpa using hln
  · have hln : lnN ell M R i = ell ^ 1 := rowLen_of_isRowN hg h
    have hd := (isRowN_dvd h).1
    have hv : neP0 ell M R + x < neP0 ell M R + stN ell M R i + ell ^ 1 := by
      rw [stN_succ, hln] at hs2; omega
    have hdiv : (neP0 ell M R + x) / ell ^ 1 = (neP0 ell M R + stN ell M R i) / ell ^ 1 := by
      obtain ⟨q, hq⟩ := hd
      rw [hq]
      rw [Nat.mul_div_cancel_left _ (pow_pos (by have := hg.hell; omega) 1)]
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; omega
      · rw [add_mul, one_mul, mul_comm]; omega
    have hlev : 1 = levN ell M R (neP0 ell M R + x) := by
      rw [← row_unique hg hI (show 1 ≤ 2 by norm_num)]
      have e : ell ^ 1 * ((neP0 ell M R + x) / ell ^ 1) = neP0 ell M R + stN ell M R i := by
        rw [hdiv]; exact (Nat.mul_div_cancel' (by obtain ⟨q, hq⟩ := hd; exact ⟨q, hq⟩))
      rw [e]; exact h
    refine ⟨?_, ?_⟩
    · unfold rstartN; rw [← hlev, hdiv]; exact (Nat.mul_div_cancel' hd).symm
    · rw [← hlev]; exact hln
  · have hln : lnN ell M R i = ell ^ 2 := rowLen_of_isRowN hg h
    have hd := (isRowN_dvd h).1
    have hv : neP0 ell M R + x < neP0 ell M R + stN ell M R i + ell ^ 2 := by
      rw [stN_succ, hln] at hs2; omega
    have hdiv : (neP0 ell M R + x) / ell ^ 2 = (neP0 ell M R + stN ell M R i) / ell ^ 2 := by
      obtain ⟨q, hq⟩ := hd
      rw [hq]
      rw [Nat.mul_div_cancel_left _ (pow_pos (by have := hg.hell; omega) 2)]
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; omega
      · rw [add_mul, one_mul, mul_comm]; omega
    have hlev : 2 = levN ell M R (neP0 ell M R + x) := by
      rw [← row_unique hg hI (show 2 ≤ 2 by norm_num)]
      have e : ell ^ 2 * ((neP0 ell M R + x) / ell ^ 2) = neP0 ell M R + stN ell M R i := by
        rw [hdiv]; exact (Nat.mul_div_cancel' hd)
      rw [e]; exact h
    refine ⟨?_, ?_⟩
    · unfold rstartN; rw [← hlev, hdiv]; exact (Nat.mul_div_cancel' hd).symm
    · rw [← hlev]; exact hln

#print axioms chain_row_level

end AdalyFormal.CoverOmega
