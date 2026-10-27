import Mathlib

/-!
# CvC1 -- the local test vector at `c_loc` has NEGATIVE energy (lane cover_jacobi_20261016)

Row `r0` of `L = n + 1` slices whose FIRST slice carries the layer (offset `o = 0`; this is the nested instance for `ell = 3`:
`C - A' = 12 ell M = 4 ell^2 M`).  Slices are numbered `j = 0..n` FROM THE RIGHT END of the row (`j = n` is the layer slice).
With the layer weight `c = cLoc n = -6/((n-1)(n+4))` (the zero of the local scalar `A(c)`), the vector
`locVec n j = -j(j+1)/2` (`j < n`), `locVec n n = (n-1) n (n+1)/6` has block sum zero and the chain energy
`c f_n^2 + c (f_n - f_{n-1})^2 + sum_{j<n-1} (f_{j+1} - f_j)^2` (the layer edges `(C-1,C)` and `(C,C+1)` carry `c`, all other edges
of the row carry `1`, the vector vanishes outside the row) equals `-n(n-1)(n+1)^2(n+2)/(3(n+4)) < 0` for `n >= 2`.
Consequence (paper): `lambda_min(c_loc) < 0`, so the first crossing `c*` of the chain satisfies `c* > c_loc` and `A(c*) != 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

noncomputable def locVec (n j : ℕ) : ℝ :=
  if j < n then -((j : ℝ) * (j + 1) / 2) else (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + 1) / 6

noncomputable def cLoc (n : ℕ) : ℝ := -6 / (((n : ℝ) - 1) * ((n : ℝ) + 4))

theorem sum_tri (n : ℕ) : ∑ j ∈ range n, (j : ℝ) * (j + 1) / 2 = ((n : ℝ) - 1) * n * (n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_sqpos (n : ℕ) : ∑ j ∈ range n, ((j : ℝ) + 1) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- the row sum of the local vector vanishes. -/
theorem locVec_sum (n : ℕ) : ∑ j ∈ range (n + 1), locVec n j = 0 := by
  rw [sum_range_succ]
  have h : ∑ j ∈ range n, locVec n j = -(∑ j ∈ range n, (j : ℝ) * (j + 1) / 2) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun j hj => by simp [locVec, (mem_range.mp hj)])
  rw [h, sum_tri]
  simp [locVec]
  ring

/-- the chain energy of the zero-extended local vector at layer weight `c`. -/
noncomputable def locEnergy (n : ℕ) (c : ℝ) : ℝ :=
  c * (locVec n n) ^ 2 + c * (locVec n n - locVec n (n - 1)) ^ 2 + ∑ j ∈ range (n - 1), (locVec n (j + 1) - locVec n j) ^ 2

theorem locEnergy_closed (k : ℕ) :
    locEnergy (k + 2) (cLoc (k + 2)) =
      -(((k : ℝ) + 2) * ((k : ℝ) + 1) * ((k : ℝ) + 3) ^ 2 * ((k : ℝ) + 4)) / (3 * ((k : ℝ) + 6)) := by
  have h1 : ∑ j ∈ range (k + 2 - 1), (locVec (k + 2) (j + 1) - locVec (k + 2) j) ^ 2 = ∑ j ∈ range (k + 1), ((j : ℝ) + 1) ^ 2 := by
    apply sum_congr (by simp)
    intro j hj
    have hj' : j < k + 1 := by simpa using hj
    have e1 : j + 1 < k + 2 := by omega
    have e2 : j < k + 2 := by omega
    simp only [locVec, if_pos e1, if_pos e2]
    push_cast
    ring
  have h2 : locVec (k + 2) (k + 2 - 1) = -(((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) := by
    have : k + 2 - 1 < k + 2 := by omega
    have e : k + 2 - 1 = k + 1 := by omega
    simp only [locVec, e, if_pos (by omega : k + 1 < k + 2)]
    push_cast
    ring
  have h3 : locVec (k + 2) (k + 2) = ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) / 6 := by
    simp only [locVec, if_neg (lt_irrefl _)]
    push_cast
    ring
  unfold locEnergy cLoc
  rw [h1, h2, h3, sum_sqpos]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk6 : ((k : ℝ) + 6) ≠ 0 := by positivity
  have hk5 : (((k + 2 : ℕ) : ℝ) - 1) * (((k + 2 : ℕ) : ℝ) + 4) ≠ 0 := by
    push_cast
    have : ((k : ℝ) + 2 - 1) * ((k : ℝ) + 2 + 4) = ((k : ℝ) + 1) * ((k : ℝ) + 6) := by ring
    rw [this]; positivity
  push_cast
  rw [show ((k : ℝ) + 2 - 1) = (k : ℝ) + 1 by ring, show ((k : ℝ) + 2 + 4) = (k : ℝ) + 6 by ring]
  field_simp
  ring

theorem locEnergy_neg (k : ℕ) : locEnergy (k + 2) (cLoc (k + 2)) < 0 := by
  rw [locEnergy_closed]
  have : 0 < ((k : ℝ) + 2) * ((k : ℝ) + 1) * ((k : ℝ) + 3) ^ 2 * ((k : ℝ) + 4) := by positivity
  have h6 : 0 < 3 * ((k : ℝ) + 6) := by positivity
  exact div_neg_of_neg_of_pos (by linarith) h6

theorem cLoc_neg (k : ℕ) : cLoc (k + 2) < 0 := by
  unfold cLoc
  have : 0 < (((k + 2 : ℕ) : ℝ) - 1) * (((k + 2 : ℕ) : ℝ) + 4) := by
    push_cast
    have : 0 < ((k : ℝ) + 2 - 1) := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have : 0 < ((k : ℝ) + 2 + 4) := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    positivity
  exact div_neg_of_neg_of_pos (by norm_num) this

#print axioms locVec
#print axioms cLoc
#print axioms sum_tri
#print axioms sum_sqpos
#print axioms locVec_sum
#print axioms locEnergy
#print axioms locEnergy_closed
#print axioms locEnergy_neg
#print axioms cLoc_neg

end AdalyFormal.CoverJacobi
