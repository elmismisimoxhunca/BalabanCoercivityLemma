import NsCvOG2

/-!
# CvOG3 -- the recursion `stN` hits `Q0`; the row structure `RowGeomD` of the nested chain (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

variable {ell M R : ℕ}

/-- row length at relative index `i`. -/
noncomputable def lnN (ell M R : ℕ) (i : ℕ) : ℕ := rowLenN ell M R (neP0 ell M R + stN ell M R i)

theorem stN_succ (i : ℕ) : stN ell M R (i + 1) = stN ell M R i + lnN ell M R i := rfl
theorem stN_zero : stN ell M R 0 = 0 := rfl

theorem rowLen_pos (hg : NGeo ell M R) (v : ℕ) : 1 ≤ rowLenN ell M R v := by
  unfold rowLenN
  split_ifs
  · exact le_rfl
  · exact Nat.one_le_pow _ _ (by have := hg.hell; omega)
  · have := hg.hell; omega

theorem stN_ge (hg : NGeo ell M R) (i : ℕ) : i ≤ stN ell M R i := by
  induction i with
  | zero => simp [stN_zero]
  | succ i ih => rw [stN_succ]; have := rowLen_pos hg (neP0 ell M R + stN ell M R i); unfold lnN; omega

theorem isStart_P0 (hg : NGeo ell M R) : isStart ell M R (neP0 ell M R) := by
  apply isStart_0
  simp only [isRowN, reg0]
  have := hg.hP0P1
  omega

/-- the tiling invariant. -/
theorem stN_inv (hg : NGeo ell M R) : ∀ i, (∀ j, j < i → neP0 ell M R + stN ell M R j < neQ0 ell M R) →
    neP0 ell M R + stN ell M R i ≤ neQ0 ell M R ∧
      (neP0 ell M R + stN ell M R i < neQ0 ell M R → isStart ell M R (neP0 ell M R + stN ell M R i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    have := hg.hP0P1
    have := hg.hQ1Q0
    have := hg.hP1A
    have := hg.hAB'
    have := hg.hB'A
    have := hg.hAB
    have := hg.hBQ1
    refine ⟨by simp [stN_zero]; omega, fun _ => by simpa [stN_zero] using isStart_P0 hg⟩
  | succ i ih =>
    intro hlt
    obtain ⟨h1, h2⟩ := ih (fun j hj => hlt j (by omega))
    have hs := h2 (hlt i (by omega))
    obtain ⟨t1, t2, -, -⟩ := tile_step hg hs
    have e : neP0 ell M R + stN ell M R (i + 1) = neP0 ell M R + stN ell M R i + rowLenN ell M R (neP0 ell M R + stN ell M R i) := by
      rw [stN_succ]; unfold lnN; ring
    rw [e]
    refine ⟨t1, fun hlt' => ?_⟩
    rcases t2 with h | h
    · omega
    · exact h

theorem exists_hit (hg : NGeo ell M R) : ∃ i, neP0 ell M R + stN ell M R i = neQ0 ell M R := by
  classical
  have hex : ∃ i, neQ0 ell M R ≤ neP0 ell M R + stN ell M R i := by
    refine ⟨nN ell M R, ?_⟩
    have := stN_ge hg (nN ell M R)
    unfold nN at *
    have h1 := hg.hP0P1; have h2 := hg.hP1A; have h3 := hg.hAB'; have h4 := hg.hB'A; have h5 := hg.hAB; have h6 := hg.hBQ1; have h7 := hg.hQ1Q0
    omega
  let i0 := Nat.find hex
  have hi0 : neQ0 ell M R ≤ neP0 ell M R + stN ell M R i0 := Nat.find_spec hex
  have hmin : ∀ j, j < i0 → neP0 ell M R + stN ell M R j < neQ0 ell M R := by
    intro j hj
    have := Nat.find_min hex hj
    omega
  have := (stN_inv hg i0 hmin).1
  exact ⟨i0, by omega⟩

end AdalyFormal.CoverOmega
