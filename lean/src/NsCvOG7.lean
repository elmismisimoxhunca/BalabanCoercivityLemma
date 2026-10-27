import NsCvOG6

/-!
# CvOG7 -- the layer row and the fat-region rows of the nested chain (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem hit_of_nojump (hg : NGeo ell M R) {T : ℕ} (hT0 : neP0 ell M R < T) (hTQ : T ≤ neQ0 ell M R)
    (hnj : ∀ v, isStart ell M R v → v < T → v + rowLenN ell M R v ≤ T) :
    ∃ i, i ≤ RN hg ∧ neP0 ell M R + stN ell M R i = T := by
  classical
  have hex : ∃ i, T ≤ neP0 ell M R + stN ell M R i := ⟨RN hg, by have := RN_hit hg; omega⟩
  have hge : T ≤ neP0 ell M R + stN ell M R (Nat.find hex) := Nat.find_spec hex
  have hle : Nat.find hex ≤ RN hg := Nat.find_min' hex (by have := RN_hit hg; omega)
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have h0 : Nat.find hex = 0 := by omega
    rw [h0, stN_zero] at hge
    omega
  have hprev : neP0 ell M R + stN ell M R (Nat.find hex - 1) < T := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  have hstart := RN_start hg (Nat.find hex - 1) (by omega)
  have h1 := hnj _ hstart hprev
  have e : neP0 ell M R + stN ell M R (Nat.find hex) = neP0 ell M R + stN ell M R (Nat.find hex - 1) + rowLenN ell M R (neP0 ell M R + stN ell M R (Nat.find hex - 1)) := by
    have : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [stN_succ]; unfold lnN; ring
  exact ⟨Nat.find hex, hle, by omega⟩

/-- the layer slice is a level-2 row start (needs `ell ∣ M`). -/
theorem layer_dvd (hg : NGeo ell M R) : ell ^ 2 ∣ neC ell M R := by
  obtain ⟨m', hm'⟩ := hg.hdell
  have h1 := hg.dA'
  have h2 : ell ^ 2 ∣ CfData.cf * (ell * M) := ⟨CfData.cf * m', by rw [hm']; ring⟩
  unfold neC
  exact dvd_add h1 h2

theorem layer_lo (hg : NGeo ell M R) : neA' ell M R ≤ neC ell M R := by unfold neC; omega

theorem layer_hi (hg : NGeo ell M R) : neC ell M R + ell ^ 2 ≤ neB' ell M R := by
  have h2 : ell ^ 2 ∣ neB' ell M R := hg.dB'
  have h1 := layer_dvd hg
  have hlt : neC ell M R < neB' ell M R := by
    have := hg.hdell
    unfold neC neB' neA'
    obtain ⟨m', hm'⟩ := hg.hdell
    have hM : 0 < M := Nat.pos_of_ne_zero (by intro h0; have := hg.cRM; rw [h0] at this; simp at this)
    have hell := hg.hell
    -- 12 (ell M) + ell^2 (R M + M) < ell^2 (R M) + 12 ell^2 M  iff 12 ell M < 11 ell^2 M
    obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c2 (M := M) hell
    have hY : 0 < ell * (ell * M) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hM)
    omega
  exact step_align _ _ _ h1 h2 hlt

theorem hit_C (hg : NGeo ell M R) : ∃ i, i ≤ RN hg ∧ neP0 ell M R + stN ell M R i = neC ell M R := by
  have hlo := layer_lo hg
  have hhi := layer_hi hg
  have hP := hg.hP0P1; have h1 := hg.hP1A; have h2 := hg.hAB'; have h3 := hg.hB'A; have h4 := hg.hAB; have h5 := hg.hBQ1; have h6 := hg.hQ1Q0
  refine hit_of_nojump hg (by omega) (by omega) ?_
  intro v hv hvC
  have hdell := hg.dA'l
  rcases hv with h | h | h
  · have hr : rowLenN ell M R v = 1 := rowLen_0 v h
    rw [hr]; omega
  · simp only [isRowN, reg1] at h
    obtain ⟨hdv, ⟨hP', hQ'⟩, hn2⟩ := h
    have hn0 : ¬ reg0 ell M R v := by unfold reg0; omega
    rw [rowLen_1 v hn0 hn2]
    unfold reg2 at hn2
    have hvA : v < neA' ell M R := by omega
    have := step_align ell v _ hdv hdell hvA
    omega
  · simp only [isRowN] at h
    obtain ⟨hdv, h2'⟩ := h
    have hn0 : ¬ reg0 ell M R v := fun h0 => reg0_not_reg2 hg h0 h2'
    rw [rowLen_2 v hn0 h2']
    exact step_align _ v _ hdv (layer_dvd hg) hvC

end AdalyFormal.CoverOmega
