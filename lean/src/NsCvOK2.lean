import NsCvOK1
import CvJ5

/-!
# CvOK2 -- forward zero-propagation through the row before the layer and through the layer row (lane omega)

* `prevRow_fwd_zero`: a flat row of length `L >= 2` whose LAST slice equation is NOT flat (it sees the layer weight): from a zero incoming state, the first `L - 1` flat equations plus the row sum force `m = 0` and `e = 0` on the row.
* `layer_fwd_zero`: the layer row (weights `c` on its first two edges) with zero incoming state, row sum zero and the nondegeneracy `hnl`: `m = 0`, `e = 0` on the row, zero outgoing state.
(Forward counterparts of CvJ `blocks_back_zero` / `layerRow_zero`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

theorem prevRow_fwd_zero {s : ℤ} {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {m : ℝ}
    (hel : BlockELs s (L - 1) e m) (hs : BlockSums s L e) (hE : e s = 0) (hF : e s - e (s - 1) = 0) :
    m = 0 ∧ ∀ j : ℕ, j < L → e (s + j) = 0 := by
  have hcl := fun j (hj : j ≤ L - 1) => (blocks_closed hel j hj).1
  have hc2 : ∀ j ∈ Finset.range L, e (s + j) = -(m * ((j : ℝ) * (j + 1) / 2)) := by
    intro j hj
    have := hcl j (by have := Finset.mem_range.mp hj; omega)
    have hEm : e (s - 1) = 0 := by linarith
    rw [this, hE, hEm]; ring
  unfold BlockSums at hs
  rw [Finset.sum_congr rfl hc2, Finset.sum_neg_distrib, ← Finset.mul_sum, sumR_tri] at hs
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hm : m = 0 := by
    have hne : (((L : ℝ) - 1) * L * (L + 1) / 6) ≠ 0 := by
      have : 0 < (L : ℝ) - 1 := by linarith
      positivity
    have : m * (((L : ℝ) - 1) * L * (L + 1) / 6) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hne
  refine ⟨hm, fun j hj => ?_⟩
  rw [hc2 j (Finset.mem_range.mpr hj), hm]; ring

theorem layer_fwd_zero {s : ℤ} {L : ℕ} (hL : 3 ≤ L) {e : ℤ → ℝ} {m c : ℝ} (hc : c ≠ 0)
    (hel : LayerELs s L e m c) (hsum : BlockSums s L e)
    (hE : e s = 0) (hF : e s - e (s - 1) = 0)
    (hnl : ((L : ℝ) - 2) * ((L : ℝ) + 3) / 6 + 1 / c ≠ 0) :
    m = 0 ∧ (∀ j : ℕ, j ≤ L → e (s + j) = 0) ∧ e (s + L) - e (s + L - 1) = 0 := by
  obtain ⟨h0, h1, hflat⟩ := hel
  have hEm : e (s - 1) = 0 := by linarith
  have e1 : e (s + 1) = -m / c := by
    rw [hE, hEm] at h0
    have : c * e (s + 1) = -m := by linarith
    field_simp
    linarith
  -- closed form g(j) = -m (1/c + j(j+1)/2 - 1), j >= 1
  set g : ℕ → ℝ := fun j => -m * (1 / c + (j : ℝ) * (j + 1) / 2 - 1) with hg
  have hg1 : e (s + 1) = g 1 := by
    rw [e1, hg]; simp only [Nat.cast_one]; field_simp; ring
  have hg2 : e (s + 2) = g 2 := by
    rw [hE] at h1
    have h1' : c * (e (s + 1) - 0) - (e (s + 2) - e (s + 1)) = m := h1
    rw [hg]
    simp only [Nat.cast_ofNat]
    have : e (s + 2) = (c + 1) * e (s + 1) - m := by linarith
    rw [this, e1]; field_simp; ring
  have hall : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ L → e (s + j) = g j ∧ e (s + j + 1) = g (j + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      refine ⟨by simpa using hg1, ?_⟩
      have : (s + ((1 : ℕ) : ℤ) + 1 : ℤ) = s + 2 := by push_cast; ring
      rw [this, hg2]
    | succ j hj ih =>
      intro hjL
      obtain ⟨a, b⟩ := ih (by omega)
      have b' : e (s + ((j + 1 : ℕ) : ℤ)) = g (j + 1) := by
        have : s + ((j + 1 : ℕ) : ℤ) = s + j + 1 := by push_cast; ring
        rw [this]; exact b
      refine ⟨b', ?_⟩
      have hel' := hflat (j + 1) (by omega) (by omega)
      have e2 : s + ((j + 1 : ℕ) : ℤ) - 1 = s + j := by push_cast; ring
      have e3 : s + ((j + 1 : ℕ) : ℤ) + 1 = s + ((j + 1 : ℕ) : ℤ) + 1 := rfl
      have e4 : s + ((j + 1 : ℕ) : ℤ) = s + j + 1 := by push_cast; ring
      rw [e2] at hel'
      rw [e4] at hel' ⊢
      have : e (s + j + 1 + 1) = 2 * e (s + j + 1) - e (s + j) - m := by linarith
      push_cast
      rw [this, a, b, hg]
      push_cast
      ring
  -- row sum
  have hsplit : ∑ j ∈ Finset.range L, e (s + j) = e s + ∑ j ∈ Finset.range (L - 1), e (s + ((j + 1 : ℕ) : ℤ)) := by
    have hL' : L = (L - 1) + 1 := by omega
    conv_lhs => rw [hL']
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero]
    ring
  have hrest : ∑ j ∈ Finset.range (L - 1), e (s + ((j + 1 : ℕ) : ℤ)) = ∑ j ∈ Finset.range (L - 1), g (j + 1) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := (hall (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)).1
    exact this
  have hgs : ∑ j ∈ Finset.range (L - 1), g (j + 1) = -m * (((L : ℝ) - 1) * (1 / c + (L : ℝ) * ((L : ℝ) + 1) / 6 - 1)) := by
    have : ∀ j ∈ Finset.range (L - 1), g (j + 1) = -m * (1 / c - 1) + (-m) * ((((j + 1 : ℕ) : ℝ)) * (((j + 1 : ℕ) : ℝ) + 1) / 2) := by
      intro j _
      rw [hg]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
    -- Σ_{j<L-1} (j+1)(j+2)/2 = Σ_{j<L} j(j+1)/2
    have hsh : ∑ j ∈ Finset.range (L - 1), (((j + 1 : ℕ) : ℝ)) * (((j + 1 : ℕ) : ℝ) + 1) / 2 = ((L : ℝ) - 1) * L * (L + 1) / 6 := by
      have := sumR_tri L
      have hL' : L = (L - 1) + 1 := by omega
      conv at this => rw [hL']
      rw [Finset.sum_range_succ'] at this
      simp only [Nat.cast_zero, zero_mul, zero_add, zero_div, add_zero] at this
      have hLc : (((L - 1 + 1 : ℕ) : ℝ)) = L := by exact_mod_cast (by omega : L - 1 + 1 = L)
      rw [hLc] at this
      exact this
    rw [hsh, nsmul_eq_mul]
    have : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
      have h' : (L - 1 : ℕ) + 1 = L := by omega
      have h'' : (((L - 1 : ℕ) : ℝ)) + 1 = L := by exact_mod_cast h'
      linarith
    rw [this]; ring
  have hsum' : -m * (((L : ℝ) - 1) * (1 / c + (L : ℝ) * ((L : ℝ) + 1) / 6 - 1)) = 0 := by
    have := hsum
    unfold BlockSums at this
    rw [hsplit, hrest, hgs, hE] at this
    linarith
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hm0 : m = 0 := by
    have hfac : (1 / c + (L : ℝ) * ((L : ℝ) + 1) / 6 - 1) = ((L : ℝ) - 2) * ((L : ℝ) + 3) / 6 + 1 / c := by ring
    rw [hfac] at hsum'
    have hLm : ((L : ℝ) - 1) ≠ 0 := by linarith
    rcases mul_eq_zero.mp hsum' with h | h
    · linarith
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hLm
      · exact absurd h' hnl
  have hg0 : ∀ j : ℕ, g j = 0 := by intro j; rw [hg, hm0]; ring
  refine ⟨hm0, ?_, ?_⟩
  · intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjp
    · subst hj0; simpa using hE
    · by_cases hjL : j = L
      · subst hjL
        have := (hall (j - 1) (by omega) (by omega)).2
        have e5 : s + ((j - 1 : ℕ) : ℤ) + 1 = s + j := by
          have : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          rw [this]; ring
        rw [e5] at this
        rw [this, show j - 1 + 1 = j by omega, hg0]
      · have := (hall j hjp (by omega)).1
        rw [this, hg0]
  · have hLz : e (s + L) = 0 := by
      have := (hall (L - 1) (by omega) (by omega)).2
      have e5 : s + ((L - 1 : ℕ) : ℤ) + 1 = s + L := by
        have : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
        rw [this]; ring
      rw [e5] at this
      rw [this, show L - 1 + 1 = L by omega, hg0]
    have hLz1 : e (s + L - 1) = 0 := by
      have := (hall (L - 1) (by omega) (by omega)).1
      have e5 : s + ((L - 1 : ℕ) : ℤ) = s + L - 1 := by
        have : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
        rw [this]; ring
      rw [e5] at this
      rw [this, hg0]
    rw [hLz, hLz1]; ring

#print axioms prevRow_fwd_zero
#print axioms layer_fwd_zero

end AdalyFormal.CoverOmega
