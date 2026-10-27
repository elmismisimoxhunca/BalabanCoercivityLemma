import NsCvOG7

/-!
# CvOG8 -- all chain data of the nested instance in the form needed by `chain_poleD` (lane omega)

`nested_chain_data`: the layer row `i0` (start `neC`, length `ell²`), and the window of `ell` consecutive level-2 rows of the fat region starting at the first unit slice `u0 = M(2R+14)`
of `neLam` (fine start `ell² u0`), all in the interior of the chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

variable {ell M R : ℕ}

theorem hit_aligned2 (hg : NGeo ell M R) {T : ℕ} (hT : ell ^ 2 ∣ T) (hT0 : neP0 ell M R < T) (hTQ : T ≤ neQ0 ell M R) :
    ∃ i, i ≤ RN hg ∧ neP0 ell M R + stN ell M R i = T := by
  refine hit_of_nojump hg hT0 hTQ ?_
  intro v hv hvT
  have hℓ : ell ∣ T := dvd_trans (dvd_pow_self ell (by norm_num)) hT
  rcases hv with h | h | h
  · rw [rowLen_0 v h]; omega
  · simp only [isRowN, reg1] at h
    obtain ⟨hdv, ⟨hP', hQ'⟩, hn2⟩ := h
    have hn0 : ¬ reg0 ell M R v := by unfold reg0; omega
    rw [rowLen_1 v hn0 hn2]
    exact step_align ell v _ hdv hℓ hvT
  · simp only [isRowN] at h
    obtain ⟨hdv, h2'⟩ := h
    have hn0 : ¬ reg0 ell M R v := fun h0 => reg0_not_reg2 hg h0 h2'
    rw [rowLen_2 v hn0 h2']
    exact step_align _ v _ hdv hT hvT

/-- consecutive level-2 rows. -/
theorem stN_level2_succ (hg : NGeo ell M R) {i : ℕ} (hv : isRowN ell M R 2 (neP0 ell M R + stN ell M R i)) :
    lnN ell M R i = ell ^ 2 := by
  simp only [isRowN] at hv
  obtain ⟨hdv, h2⟩ := hv
  have hn0 : ¬ reg0 ell M R (neP0 ell M R + stN ell M R i) := fun h0 => reg0_not_reg2 hg h0 h2
  unfold lnN; exact rowLen_2 _ hn0 h2

/-- the first unit slice of `neLam`, in unit coordinates. -/
def u0N (M R : ℕ) : ℕ := M * (2 * R + (CfData.cf + 2)) + 1

theorem fat_bounds (hg : NGeo ell M R) (hM : ell ≤ M) {j : ℕ} (hj : j ≤ ell) :
    neA ell M R ≤ ell ^ 2 * (u0N M R + j) ∧ ell ^ 2 * (u0N M R + j) < neB ell M R := by
  have hM0 : 0 < M := by have := hg.cRM; exact Nat.pos_of_ne_zero (by intro h0; rw [h0] at this; simp at this)
  have hRM := hg.hell
  unfold u0N neA neB
  constructor
  · nlinarith [Nat.mul_le_mul hRM hRM, Nat.zero_le (ell * ell * (R * M)), Nat.zero_le (ell * ell * M)]
  · nlinarith [Nat.mul_le_mul hRM hRM, Nat.mul_le_mul_left (ell * ell) hM, Nat.mul_le_mul_left (ell * ell) hj, Nat.zero_le (ell * ell * (R * M))]

theorem fat_reg2 (hg : NGeo ell M R) (hM : ell ≤ M) {j : ℕ} (hj : j ≤ ell) :
    isRowN ell M R 2 (ell ^ 2 * (u0N M R + j)) := by
  simp only [isRowN]
  refine ⟨⟨u0N M R + j, rfl⟩, ?_⟩
  simp only [reg2]
  right
  exact fat_bounds hg hM hj

theorem fat_rows (hg : NGeo ell M R) (hM : ell ≤ M) {i1 : ℕ} (hi1 : neP0 ell M R + stN ell M R i1 = ell ^ 2 * u0N M R) :
    ∀ j, j ≤ ell → neP0 ell M R + stN ell M R (i1 + j) = ell ^ 2 * (u0N M R + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using hi1
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R (i1 + j)) := by
      rw [h1]; exact fat_reg2 hg hM (by omega)
    have hl := stN_level2_succ hg hreg
    have e : stN ell M R (i1 + (j + 1)) = stN ell M R (i1 + j) + lnN ell M R (i1 + j) := by
      rw [← Nat.add_assoc]; exact stN_succ _
    have e2 : ell ^ 2 * (u0N M R + (j + 1)) = ell ^ 2 * (u0N M R + j) + ell ^ 2 := by ring
    rw [e, hl]; omega

end AdalyFormal.CoverOmega
