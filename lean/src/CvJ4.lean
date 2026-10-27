import CvJ3

/-!
# CvJ4 -- the layer row (lane cover_jacobi_20261016)

The row `r0 = [s, s + L)` whose FIRST slice `s` is the layer slice: the edges `(s-1,s)` and `(s,s+1)` carry the weight `c`, every other edge of the row weight 1.
Euler-Lagrange identities (`LayerELs`): at `s`: `c (e_s - e_{s-1}) - c (e_{s+1} - e_s) = m`; at `s+1`: `c (e_{s+1} - e_s) - (e_{s+2} - e_{s+1}) = m`; at `s+j`, `2 <= j < L`: `2 e - e^- - e^+ = m`.
`layerRow_zero`: if the END state of the row vanishes (`e_{s+L} = 0`, `e_{s+L} - e_{s+L-1} = 0`), the row sum is zero, `c != 0` and
`(L-2)(L+3)/6 + 1/c != 0` (i.e. `c != c_loc`), then `m = 0`, `e` vanishes on the row and `e_{s-1} = 0`: a zero END state forces a zero START state.
If `(L-2)(L+3)/6 + 1/c = 0` the conclusion can fail (the local mode of CvC1).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

def LayerELs (s : ℤ) (L : ℕ) (e : ℤ → ℝ) (m c : ℝ) : Prop :=
  c * (e s - e (s - 1)) - c * (e (s + 1) - e s) = m ∧
  c * (e (s + 1) - e s) - (e (s + 2) - e (s + 1)) = m ∧
  ∀ j : ℕ, 2 ≤ j → j < L → 2 * e (s + j) - e (s + j - 1) - e (s + j + 1) = m

theorem sumR_tri (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) * (j + 1) / 2 = ((n : ℝ) - 1) * n * (n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- the backward closed form `f_k = -m (k-1) k / 2`. -/
noncomputable def fq (m : ℝ) (k : ℕ) : ℝ := -m * (((k : ℝ) - 1) * k / 2)

/-- backward closed form on the flat part of the layer row. -/
theorem layerRow_closed {s : ℤ} {L : ℕ} (hL : 3 ≤ L) {e : ℤ → ℝ} {m : ℝ}
    (hflat : ∀ j : ℕ, 2 ≤ j → j < L → 2 * e (s + j) - e (s + j - 1) - e (s + j + 1) = m)
    (hE : e (s + L) = 0) (hF : e (s + L) - e (s + L - 1) = 0) :
    ∀ k : ℕ, k + 1 ≤ L - 1 → e (s + L - (k : ℤ)) = fq m k ∧ e (s + L - ((k + 1 : ℕ) : ℤ)) = fq m (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simpa [fq] using hE, ?_⟩
    have e1 : s + L - ((0 + 1 : ℕ) : ℤ) = s + L - 1 := by push_cast; ring
    rw [e1]
    have : e (s + L - 1) = 0 := by linarith
    rw [this]; simp [fq]
  | succ k ih =>
    intro hk
    obtain ⟨h0, h1⟩ := ih (by omega)
    have hx := hflat (L - k - 1) (by omega) (by omega)
    have hcast : ((L - k - 1 : ℕ) : ℤ) = (L : ℤ) - k - 1 := by omega
    have e1 : s + ((L - k - 1 : ℕ) : ℤ) = s + L - ((k + 1 : ℕ) : ℤ) := by
      rw [hcast]; push_cast; ring
    have e2 : s + ((L - k - 1 : ℕ) : ℤ) - 1 = s + L - ((k + 1 + 1 : ℕ) : ℤ) := by
      rw [hcast]; push_cast; ring
    have e3 : s + ((L - k - 1 : ℕ) : ℤ) + 1 = s + L - (k : ℤ) := by
      rw [hcast]; ring
    rw [e2, e3, e1] at hx
    refine ⟨h1, ?_⟩
    rw [h0, h1] at hx
    unfold fq at hx ⊢
    push_cast at hx ⊢
    nlinarith [hx]

theorem layerRow_zero {s : ℤ} {L : ℕ} (hL : 3 ≤ L) {e : ℤ → ℝ} {m c : ℝ} (hc : c ≠ 0)
    (hel : LayerELs s L e m c) (hsum : BlockSums s L e)
    (hE : e (s + L) = 0) (hF : e (s + L) - e (s + L - 1) = 0)
    (hnl : ((L : ℝ) - 2) * ((L : ℝ) + 3) / 6 + 1 / c ≠ 0) :
    m = 0 ∧ (∀ j : ℕ, j ≤ L → e (s + j) = 0) ∧ e (s - 1) = 0 := by
  obtain ⟨hs0, hs1, hflat⟩ := hel
  have hcl := layerRow_closed hL hflat hE hF
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  -- e(s+1) and e(s+2)
  have hk := hcl (L - 2) (by omega)
  have hidx1 : s + (L : ℤ) - (((L - 2 + 1 : ℕ)) : ℤ) = s + 1 := by
    have : ((L - 2 + 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
    rw [this]; ring
  have hidx2 : s + (L : ℤ) - ((L - 2 : ℕ) : ℤ) = s + 2 := by
    have : ((L - 2 : ℕ) : ℤ) = (L : ℤ) - 2 := by omega
    rw [this]; ring
  rw [hidx1] at hk
  rw [hidx2] at hk
  obtain ⟨he2, he1⟩ := hk
  have hcastL2 : (((L - 2 : ℕ) : ℝ)) = (L : ℝ) - 2 := by
    have : (L - 2 : ℕ) + 2 = L := by omega
    have h' : (((L - 2 : ℕ) : ℝ)) + 2 = L := by exact_mod_cast this
    linarith
  have hcastL1 : (((L - 2 + 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
    have h' : (((L - 2 : ℕ) : ℝ)) + 1 = ((L - 2 + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [← h', hcastL2]; ring
  unfold fq at he1 he2
  rw [hcastL1] at he1
  rw [hcastL2] at he2
  -- e_s from the EL at s+1
  have hes : e s = e (s + 1) - m * ((L : ℝ) - 1) / c := by
    have : c * (e (s + 1) - e s) = m * ((L : ℝ) - 1) := by
      rw [he1, he2] at hs1
      rw [he1]
      linear_combination hs1
    field_simp
    linarith
  -- the row sum
  have hsplit : ∑ j ∈ Finset.range L, e (s + j) = e s + ∑ j ∈ Finset.range (L - 1), e (s + ((j + 1 : ℕ) : ℤ)) := by
    have hL' : L = (L - 1) + 1 := by omega
    conv_lhs => rw [hL']
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero]
    ring
  have hrefl : ∑ j ∈ Finset.range (L - 1), e (s + ((j + 1 : ℕ) : ℤ)) = ∑ j ∈ Finset.range (L - 1), fq m (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => e (s + ((j + 1 : ℕ) : ℤ))) (L - 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjL : j < L - 1 := Finset.mem_range.mp hj
    have := (hcl j (by omega)).2
    have hidx : s + (((L - 1 - 1 - j) + 1 : ℕ) : ℤ) = s + (L : ℤ) - ((j + 1 : ℕ) : ℤ) := by
      have : (((L - 1 - 1 - j) + 1 : ℕ) : ℤ) = (L : ℤ) - j - 1 := by omega
      rw [this]; push_cast; ring
    show e (s + ((L - 1 - 1 - j + 1 : ℕ) : ℤ)) = fq m (j + 1)
    rw [hidx, this]
  have hfq : ∑ j ∈ Finset.range (L - 1), fq m (j + 1) = -m * (((L : ℝ) - 2) * ((L : ℝ) - 1) * L / 6) := by
    have : ∑ j ∈ Finset.range (L - 1), fq m (j + 1) = -m * ∑ j ∈ Finset.range (L - 1), (j : ℝ) * (j + 1) / 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold fq; push_cast; ring
    rw [this, sumR_tri]
    have : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
      have h' : (L - 1 : ℕ) + 1 = L := by omega
      have h'' : (((L - 1 : ℕ) : ℝ)) + 1 = L := by exact_mod_cast h'
      linarith
    rw [this]; ring
  have hsum' : e s + (-m * (((L : ℝ) - 2) * ((L : ℝ) - 1) * L / 6)) = 0 := by
    have := hsum
    unfold BlockSums at this
    rw [hsplit, hrefl, hfq] at this
    exact this
  have hmz : m = 0 := by
    have hc1 : 1 / c * c = 1 := by field_simp
    have key : m * (((L : ℝ) - 1) * (((L : ℝ) - 2) * ((L : ℝ) + 3) / 6 + 1 / c)) = 0 := by
      rw [he1] at hes
      have : m * (((L : ℝ) - 1) * (((L : ℝ) - 2) * ((L : ℝ) + 3) / 6 + 1 / c)) =
          -(e s + (-m * (((L : ℝ) - 2) * ((L : ℝ) - 1) * L / 6))) := by
        rw [hes]; field_simp; ring
      rw [this, hsum']; ring
    have hLm1 : ((L : ℝ) - 1) ≠ 0 := by linarith
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hLm1
      · exact absurd h' hnl
  have hf0 : ∀ k : ℕ, fq m k = 0 := by intro k; unfold fq; rw [hmz]; ring
  have hes0 : e s = 0 := by
    rw [hes, he1, hmz]; simp [hf0]
  have h1' : e (s + 1) = 0 := by rw [he1, hmz]; ring
  refine ⟨hmz, ?_, ?_⟩
  · intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simpa using hes0
    · by_cases hj1 : j = 1
      · subst hj1; simpa using h1'
      · by_cases hjL : j = L
        · subst hjL; exact hE
        · have hj2 : j < L := lt_of_le_of_ne hj hjL
          have := (hcl (L - j) (by omega)).1
          have hidx : s + (L : ℤ) - ((L - j : ℕ) : ℤ) = s + j := by
            have : ((L - j : ℕ) : ℤ) = (L : ℤ) - j := by omega
            rw [this]; ring
          rw [hidx] at this
          rw [this, hf0]
  · have : c * (e s - e (s - 1)) - c * (e (s + 1) - e s) = m := hs0
    rw [hes0, h1', hmz] at this
    have : c * (0 - e (s - 1)) = 0 := by linarith
    have : e (s - 1) = 0 := by
      have := mul_eq_zero.mp this
      rcases this with h | h
      · exact absurd h hc
      · linarith
    exact this


#print axioms LayerELs
#print axioms sumR_tri
#print axioms fq
#print axioms layerRow_closed
#print axioms layerRow_zero

end AdalyFormal.CoverJacobi
