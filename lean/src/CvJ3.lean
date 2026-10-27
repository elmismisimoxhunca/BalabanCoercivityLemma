import Mathlib

/-!
# CvJ3 -- flat rows with an ARBITRARY start (lane cover_jacobi_20261016)

CvJ1 treats blocks `[bL, bL + L)`; the chain has rows of different lengths at arbitrary starts.  Here `BlockELs s L e m` is the
Euler-Lagrange identity `2 e_x - e_{x-1} - e_{x+1} = m` on the slices `s .. s + L - 1`, `BlockSums s L e` the row sum.  Proved for every `s : Z`, `L >= 2`:
* `blocks_closed`, `blocks_sum_eq`, `blocks_step`: the forward transfer `(E,F) -> (E',F')` and the multiplier formula `m (L-1)(L+1) = 6 (E + F (L-1)/2)`;
* `blocks_back_zero`: if the END state `(e_{s+L}, e_{s+L} - e_{s+L-1})` vanishes then `m = 0`, the START state vanishes and `e` vanishes on the row
  (backward propagation of a zero state through ANY flat row);
* `blocks_fwd_zero`: if the START state vanishes then `m = 0`, the end state vanishes and `e` vanishes on the row (forward propagation).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

def BlockELs (s : ℤ) (L : ℕ) (e : ℤ → ℝ) (m : ℝ) : Prop :=
  ∀ j : ℕ, j < L → 2 * e (s + j) - e (s + j - 1) - e (s + j + 1) = m

def BlockSums (s : ℤ) (L : ℕ) (e : ℤ → ℝ) : Prop :=
  ∑ j ∈ Finset.range L, e (s + j) = 0

theorem sumR_id (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sumR_jj (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) * (j + 1) = ((n : ℝ) - 1) * n * (n + 1) / 3 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem blocks_closed {s : ℤ} {L : ℕ} {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) :
    ∀ j : ℕ, j ≤ L →
      e (s + j) = e s + j * (e s - e (s - 1)) - m * (j * (j + 1) / 2) ∧
      e (s + j) - e (s + j - 1) = (e s - e (s - 1)) - j * m := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hel := h n (by omega)
    have ha : s + ((n + 1 : ℕ) : ℤ) = s + n + 1 := by push_cast; ring
    have hb : s + n + 1 - 1 = s + n := by ring
    rw [ha, hb]
    push_cast
    constructor
    · linear_combination (-1 : ℝ) * hel + h1 + h2
    · linear_combination (-1 : ℝ) * hel + h2

theorem blocks_sum_eq {s : ℤ} {L : ℕ} {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) (hs : BlockSums s L e) :
    (L : ℝ) * e s + (e s - e (s - 1)) * ((L : ℝ) * ((L : ℝ) - 1) / 2) - m * (((L : ℝ) - 1) * L * (L + 1) / 6) = 0 := by
  have hc : ∀ j ∈ Finset.range L, e (s + j) = e s + j * (e s - e (s - 1)) - m * ((j : ℝ) * (j + 1) / 2) := by
    intro j hj
    exact (blocks_closed h j (Finset.mem_range.mp hj).le).1
  unfold BlockSums at hs
  rw [Finset.sum_congr rfl hc] at hs
  have : ∑ j ∈ Finset.range L, (e s + j * (e s - e (s - 1)) - m * ((j : ℝ) * (j + 1) / 2)) =
      (L : ℝ) * e s + (e s - e (s - 1)) * ∑ j ∈ Finset.range L, (j : ℝ) - m / 2 * ∑ j ∈ Finset.range L, (j : ℝ) * (j + 1) := by
    calc ∑ j ∈ Finset.range L, (e s + j * (e s - e (s - 1)) - m * ((j : ℝ) * (j + 1) / 2))
        = ∑ j ∈ Finset.range L, (e s + (e s - e (s - 1)) * (j : ℝ) - m / 2 * ((j : ℝ) * (j + 1))) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp
  rw [this, sumR_id, sumR_jj] at hs
  linarith

theorem blocks_step {s : ℤ} {L : ℕ} {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) :
    e (s + L) = e s + L * (e s - e (s - 1)) - m * ((L : ℝ) * (L + 1) / 2) ∧
    e (s + L) - e (s + L - 1) = (e s - e (s - 1)) - L * m := by
  have h0 := blocks_closed h L le_rfl
  exact ⟨h0.1, h0.2⟩

theorem blocks_mult {s : ℤ} {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) (hs : BlockSums s L e) :
    m * (((L : ℝ) - 1) * ((L : ℝ) + 1)) = 6 * (e s + (e s - e (s - 1)) * (((L : ℝ) - 1) / 2)) := by
  have h0 := blocks_sum_eq h hs
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := by linarith
  apply mul_left_cancel₀ hL0
  linear_combination (-6 : ℝ) * h0

/-- BACKWARD propagation of a zero state through a flat row of length `L >= 2`. -/
theorem blocks_back_zero {s : ℤ} {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) (hs : BlockSums s L e)
    (hE : e (s + L) = 0) (hF : e (s + L) - e (s + L - 1) = 0) :
    m = 0 ∧ e s = 0 ∧ e s - e (s - 1) = 0 ∧ ∀ j : ℕ, j ≤ L → e (s + j) = 0 := by
  obtain ⟨t1, t2⟩ := blocks_step h
  have hm := blocks_mult hL h hs
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  set F := e s - e (s - 1) with hFdef
  set E := e s with hEdef
  have hF0 : F = L * m := by linarith
  have hE0 : E = m * ((L : ℝ) * (1 - L) / 2) := by
    have : E + L * F - m * ((L : ℝ) * (L + 1) / 2) = 0 := by rw [← t1]; exact hE
    rw [hF0] at this
    linarith
  have hm0 : m = 0 := by
    rw [hF0, hE0] at hm
    have : m * (((L : ℝ) - 1) * ((L : ℝ) + 1)) = 0 := by linear_combination hm
    have hne : ((L : ℝ) - 1) * ((L : ℝ) + 1) ≠ 0 := by
      have : 0 < ((L : ℝ) - 1) := by linarith
      have : 0 < ((L : ℝ) + 1) := by linarith
      positivity
    exact (mul_eq_zero.mp this).resolve_right hne
  have hF1 : F = 0 := by rw [hF0, hm0]; ring
  have hE1 : E = 0 := by rw [hE0, hm0]; ring
  refine ⟨hm0, hE1, hF1, ?_⟩
  intro j hj
  have := (blocks_closed h j hj).1
  have hes : e s = 0 := hE1
  have hfl : e s - e (s - 1) = 0 := hF1
  rw [this, hfl, hes, hm0]; ring

/-- FORWARD propagation of a zero state through a flat row. -/
theorem blocks_fwd_zero {s : ℤ} {L : ℕ} (hL : 2 ≤ L) {e : ℤ → ℝ} {m : ℝ} (h : BlockELs s L e m) (hs : BlockSums s L e)
    (hE : e s = 0) (hF : e s - e (s - 1) = 0) :
    m = 0 ∧ e (s + L) = 0 ∧ e (s + L) - e (s + L - 1) = 0 ∧ ∀ j : ℕ, j ≤ L → e (s + j) = 0 := by
  have hm := blocks_mult hL h hs
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  rw [hF, hE] at hm
  have hm0 : m = 0 := by
    have hne : ((L : ℝ) - 1) * ((L : ℝ) + 1) ≠ 0 := by
      have : 0 < ((L : ℝ) - 1) := by linarith
      have : 0 < ((L : ℝ) + 1) := by linarith
      positivity
    have : m * (((L : ℝ) - 1) * ((L : ℝ) + 1)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hne
  obtain ⟨t1, t2⟩ := blocks_step h
  refine ⟨hm0, ?_, ?_, ?_⟩
  · rw [t1, hF, hE, hm0]; ring
  · rw [t2, hF, hm0]; ring
  · intro j hj
    have := (blocks_closed h j hj).1
    rw [this, hF, hE, hm0]; ring


#print axioms BlockELs
#print axioms BlockSums
#print axioms sumR_id
#print axioms sumR_jj
#print axioms blocks_closed
#print axioms blocks_sum_eq
#print axioms blocks_step
#print axioms blocks_mult
#print axioms blocks_back_zero
#print axioms blocks_fwd_zero

end AdalyFormal.CoverJacobi
