import CvOG5

/-!
# CvOG6 -- `RowGeomD` instance for the nested chain (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.CoverNested

variable {ell M R : ℕ}

/-- the row containing slice `x`. -/
noncomputable def rowOfN (ell M R x : ℕ) : ℕ := by
  classical exact if h : ∃ i, x < stN ell M R (i + 1) then Nat.find h else 0

theorem rowOfN_spec (hg : NGeo ell M R) {x : ℕ} (hx : x < nN ell M R) :
    rowOfN ell M R x < RN hg ∧ stN ell M R (rowOfN ell M R x) ≤ x ∧ x < stN ell M R (rowOfN ell M R x + 1) := by
  classical
  have hRN := RN_pos hg
  have hex : ∃ i, x < stN ell M R (i + 1) := ⟨RN hg - 1, by
    have : RN hg - 1 + 1 = RN hg := by omega
    rw [this, stN_RN hg]; exact hx⟩
  have hro : rowOfN ell M R x = Nat.find hex := by unfold rowOfN; rw [dif_pos hex]
  rw [hro]
  have hspec : x < stN ell M R (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ RN hg - 1 := Nat.find_min' hex (by
    have : RN hg - 1 + 1 = RN hg := by omega
    rw [this, stN_RN hg]; exact hx)
  refine ⟨by omega, ?_, hspec⟩
  by_cases h0 : Nat.find hex = 0
  · rw [h0, stN_zero]; omega
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [e] at this
    omega

theorem nested_rowGeom (hg : NGeo ell M R) :
    RowGeomD (nN ell M R) (RN hg) (R * M) (R * M) (stN ell M R) (lnN ell M R) (rowOfN ell M R) := by
  refine ⟨stN_zero, fun i => stN_succ i, ?_, fun i hi => lnN_left hg hi, ?_, ?_, stN_RN hg, ?_, ?_⟩
  · intro i _
    unfold lnN; exact rowLen_pos hg _
  · intro i hi hib
    have hRN := iQ_RN hg
    exact le_trans (by omega) (lnN_mid hg hi (by omega))
  · intro i hi hiR
    exact lnN_right hg (by have := iQ_RN hg; omega) hiR
  · intro i hi x hx
    constructor
    · intro h
      have hs := rowOfN_spec hg hx
      rw [h] at hs
      exact ⟨hs.2.1, by rw [← stN_succ]; exact hs.2.2⟩
    · rintro ⟨h1, h2⟩
      have hs := rowOfN_spec hg hx
      set k := rowOfN ell M R x with hk
      rcases lt_trichotomy i k with h | h | h
      · have := stN_mono hg (show i + 1 ≤ k by omega)
        rw [← stN_succ] at h2
        omega
      · exact h.symm
      · have := stN_mono hg (show k + 1 ≤ i by omega)
        omega
  · intro x hx
    have hs := rowOfN_spec hg hx
    exact ⟨_, hs.1, hs.2.1, by rw [← stN_succ]; exact hs.2.2⟩

#print axioms nested_rowGeom

end AdalyFormal.CoverOmega
