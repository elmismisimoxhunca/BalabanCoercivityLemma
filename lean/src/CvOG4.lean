import CvOG3

/-!
# CvOG4 -- `RowGeomD` for the nested chain (lane omega)

`RN` = number of rows; collar counts `a = b = R*M`; `stN`, `lnN`, `rowOfN` realise the rows `[stN i, stN i + lnN i)` of the Z-chain on the slices `[P0,Q0)` (slice `x` = `x₀ - P0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem stN_strict (hg : NGeo ell M R) (i : ℕ) : stN ell M R i < stN ell M R (i + 1) := by
  rw [stN_succ]; have := rowLen_pos hg (neP0 ell M R + stN ell M R i); unfold lnN; omega

theorem stN_mono (hg : NGeo ell M R) {i j : ℕ} (h : i ≤ j) : stN ell M R i ≤ stN ell M R j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans ih (stN_strict hg j).le

theorem stN_strictMono (hg : NGeo ell M R) {i j : ℕ} (h : i < j) : stN ell M R i < stN ell M R j :=
  lt_of_lt_of_le (stN_strict hg i) (stN_mono hg (show i + 1 ≤ j by omega))

theorem stN_inj (hg : NGeo ell M R) {i j : ℕ} (h : stN ell M R i = stN ell M R j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd h (ne_of_lt (stN_strictMono hg h'))
  · exact h'
  · exact absurd h.symm (ne_of_lt (stN_strictMono hg h'))

/-- the number of rows. -/
noncomputable def RN (hg : NGeo ell M R) : ℕ := by
  classical exact Nat.find (exists_hit hg)

theorem RN_hit (hg : NGeo ell M R) : neP0 ell M R + stN ell M R (RN hg) = neQ0 ell M R := by
  classical
  unfold RN
  exact Nat.find_spec (exists_hit hg)

theorem RN_lt (hg : NGeo ell M R) : ∀ j, j < RN hg → neP0 ell M R + stN ell M R j < neQ0 ell M R := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hlt : ∀ j', j' < j → neP0 ell M R + stN ell M R j' < neQ0 ell M R := fun j' hj' => ih j' hj' (by omega)
    have hle := (stN_inv hg j hlt).1
    have hne : neP0 ell M R + stN ell M R j ≠ neQ0 ell M R := by
      intro h
      have : Nat.find (exists_hit hg) ≤ j := Nat.find_min' (exists_hit hg) h
      unfold RN at hj
      omega
    omega

theorem RN_start (hg : NGeo ell M R) : ∀ j, j < RN hg → isStart ell M R (neP0 ell M R + stN ell M R j) := by
  intro j hj
  exact (stN_inv hg j (fun j' hj' => RN_lt hg j' (by omega))).2 (RN_lt hg j hj)

theorem RN_pos (hg : NGeo ell M R) : 0 < RN hg := by
  by_contra h
  have h0 : RN hg = 0 := by omega
  have := RN_hit hg
  rw [h0, stN_zero] at this
  have := hg.hP0P1; have := hg.hP1A; have := hg.hAB'; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1; have := hg.hQ1Q0
  omega

theorem stN_RN (hg : NGeo ell M R) : stN ell M R (RN hg) = nN ell M R := by
  have := RN_hit hg
  unfold nN
  omega

end AdalyFormal.CoverOmega
