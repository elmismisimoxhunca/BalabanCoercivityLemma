import NsCvOG4
import NsCvOK1

/-!
# CvOG5 -- `RowGeomD` for the nested chain (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem stN_left (hg : NGeo ell M R) : ∀ i, i ≤ R * M → stN ell M R i = i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hreg : reg0 ell M R (neP0 ell M R + stN ell M R i) := by
      simp only [reg0]; left; have := hg.cP; omega
    rw [stN_succ]; unfold lnN; rw [rowLen_0 _ hreg]; omega

theorem lnN_left (hg : NGeo ell M R) {i : ℕ} (hi : i < R * M) : lnN ell M R i = 1 := by
  have h1 := stN_left hg i hi.le
  have hreg : reg0 ell M R (neP0 ell M R + stN ell M R i) := by
    simp only [reg0]; left; have := hg.cP; omega
  unfold lnN; exact rowLen_0 _ hreg

/-- the index of the row starting at `Q1`. -/
noncomputable def iQ (hg : NGeo ell M R) : ℕ := by
  classical exact Nat.find (⟨RN hg, by have := RN_hit hg; have := hg.hQ1Q0; omega⟩ : ∃ i, neQ1 ell M R ≤ neP0 ell M R + stN ell M R i)

theorem iQ_hit (hg : NGeo ell M R) : neP0 ell M R + stN ell M R (iQ hg) = neQ1 ell M R := by
  classical
  have hex : ∃ i, neQ1 ell M R ≤ neP0 ell M R + stN ell M R i := ⟨RN hg, by have := RN_hit hg; have := hg.hQ1Q0; omega⟩
  have hge : neQ1 ell M R ≤ neP0 ell M R + stN ell M R (iQ hg) := Nat.find_spec hex
  have hpos : 0 < iQ hg := by
    by_contra h
    have h0 : iQ hg = 0 := by omega
    rw [h0, stN_zero] at hge
    have := hg.hP0P1; have := hg.hP1A; have := hg.hAB'; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1
    omega
  have hprev : neP0 ell M R + stN ell M R (iQ hg - 1) < neQ1 ell M R := by
    have := Nat.find_min hex (show iQ hg - 1 < iQ hg by omega)
    omega
  have hRN : iQ hg ≤ RN hg := by
    unfold iQ; exact Nat.find_min' hex (by have := RN_hit hg; have := hg.hQ1Q0; omega)
  have hstart := RN_start hg (iQ hg - 1) (by omega)
  have hstep := (tile_step hg hstart).2.2.2 hprev
  have e : neP0 ell M R + stN ell M R (iQ hg) = neP0 ell M R + stN ell M R (iQ hg - 1) + rowLenN ell M R (neP0 ell M R + stN ell M R (iQ hg - 1)) := by
    have : iQ hg = (iQ hg - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [stN_succ]; unfold lnN; ring
  omega

theorem stN_right (hg : NGeo ell M R) : ∀ k, k ≤ R * M → neP0 ell M R + stN ell M R (iQ hg + k) = neQ1 ell M R + k := by
  intro k
  induction k with
  | zero => intro _; simpa using iQ_hit hg
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hreg : reg0 ell M R (neP0 ell M R + stN ell M R (iQ hg + k)) := by
      simp only [reg0]; right; have := hg.cQ; omega
    have e : stN ell M R (iQ hg + (k + 1)) = stN ell M R (iQ hg + k) + lnN ell M R (iQ hg + k) := by
      rw [← Nat.add_assoc]; exact stN_succ _
    rw [e]
    have hl : lnN ell M R (iQ hg + k) = 1 := by unfold lnN; exact rowLen_0 _ hreg
    rw [hl]; omega

theorem iQ_RN (hg : NGeo ell M R) : RN hg = iQ hg + R * M := by
  have h1 := stN_right hg (R * M) le_rfl
  have h2 := hg.cQ
  have h3 : stN ell M R (iQ hg + R * M) = stN ell M R (RN hg) := by
    have := RN_hit hg
    omega
  exact (stN_inj hg h3).symm

theorem lnN_right (hg : NGeo ell M R) {i : ℕ} (h1 : iQ hg ≤ i) (h2 : i < RN hg) : lnN ell M R i = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = iQ hg + k := ⟨i - iQ hg, by omega⟩
  have hk : k < R * M := by have := iQ_RN hg; omega
  have hreg : reg0 ell M R (neP0 ell M R + stN ell M R (iQ hg + k)) := by
    have := stN_right hg k hk.le
    simp only [reg0]; right; have := hg.cQ; omega
  unfold lnN; exact rowLen_0 _ hreg

theorem lnN_mid (hg : NGeo ell M R) {i : ℕ} (h1 : R * M ≤ i) (h2 : i < iQ hg) : 2 ≤ lnN ell M R i := by
  have hs1 : stN ell M R (R * M) = R * M := stN_left hg _ le_rfl
  have hs2 : R * M ≤ stN ell M R i := by
    have := stN_mono hg h1; omega
  have hs3 : neP0 ell M R + stN ell M R i < neQ1 ell M R := by
    have := stN_strictMono hg h2
    have := iQ_hit hg
    omega
  have hn0 : ¬ reg0 ell M R (neP0 ell M R + stN ell M R i) := by
    simp only [reg0]; have := hg.cP; omega
  unfold lnN
  unfold rowLenN
  rw [if_neg hn0]
  have := hg.hell
  split_ifs
  · have : 2 ≤ ell ^ 2 := by nlinarith
    exact this
  · exact this

end AdalyFormal.CoverOmega
