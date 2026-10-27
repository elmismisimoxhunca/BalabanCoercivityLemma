import D1IVT

/-!
Finite Dirichlet-chain source response.  This is an exact scalar block theorem,
not an identification of the frozen lattice operators or a crossing theorem.
Unlike a fixed-source estimate, it permits the source site to be selected.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

/-- Dirichlet fine Laplacian on interior indices 1 through n. -/
def lap (y : ℕ → ℝ) (i : ℕ) : ℝ := 2 * y (i + 1) - y i - y (i + 2)

/-- Energy including the two exterior Dirichlet edges. -/
def energy (n : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), (y (i + 1) - y i) ^ 2

lemma energy_nonneg (n : ℕ) (y : ℕ → ℝ) : 0 ≤ energy n y := by
  exact sum_nonneg fun i _ => sq_nonneg _

/-- Summation by parts, retaining both boundary terms. -/
theorem energy_identity (n : ℕ) (y : ℕ → ℝ) :
    energy n y = (∑ i ∈ range n, y (i + 1) * lap y i) +
      y 0 * (y 0 - y 1) + y (n + 1) * (y (n + 1) - y n) := by
  induction n with
  | zero => simp [energy, lap]; ring
  | succ n ih =>
    unfold energy at ih ⊢
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [lap]
    ring

/-- Zero energy and one zero endpoint force every interior entry to vanish. -/
theorem eq_zero_of_energy_zero (n : ℕ) (y : ℕ → ℝ)
    (hleft : y 0 = 0) (he : energy n y = 0) :
    ∀ k ≤ n + 1, y k = 0 := by
  have hd : ∀ i < n + 1, y (i + 1) = y i := by
    intro i hi
    have hsq : (y (i + 1) - y i) ^ 2 ≤ energy n y :=
      single_le_sum (fun j _ => sq_nonneg (y (j + 1) - y j)) (mem_range.mpr hi)
    have hz : y (i + 1) - y i = 0 := by nlinarith [sq_nonneg (y (i + 1) - y i)]
    linarith
  intro k hk
  induction k with
  | zero => exact hleft
  | succ k ih =>
    rw [hd k (by omega), ih (by omega)]

/-- A nonzero coarse two-site average entails strictly positive fine energy. -/
theorem energy_pos_of_average_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hne : ∃ j < n, b j ≠ 0) : 0 < energy (2*n) y := by
  apply lt_of_le_of_ne (energy_nonneg _ _)
  intro he
  have hz := eq_zero_of_energy_zero (2*n) y hleft he.symm
  obtain ⟨j, hj, hb⟩ := hne
  have h := havg j hj
  rw [hz (2*j+1) (by omega), hz (2*j+2) (by omega)] at h
  exact hb (by linarith)

lemma sum_pair (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ range (2*n), f i) = ∑ j ∈ range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2*n+1)+1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

/-- Stationarity under opposite changes of the two entries of each block. -/
def Stationary (n : ℕ) (y : ℕ → ℝ) : Prop :=
  ∀ j < n, lap y (2*j) = lap y (2*j+1)

/-- The selected even-site source response of the constrained lift. -/
def response (y : ℕ → ℝ) (j : ℕ) : ℝ := lap y (2*j)

/-- The effective source response has exactly half the fine Dirichlet energy. -/
theorem response_energy (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) :
    2 * (∑ j ∈ range n, b j * response y j) = energy (2*n) y := by
  rw [energy_identity, hleft, hright]
  simp only [zero_mul, add_zero]
  rw [sum_pair, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hs := hstat j (mem_range.mp hj)
  have ha := havg j (mem_range.mp hj)
  simp only [response]
  rw [show 2*j+1+1 = 2*j+2 by omega, ← hs]
  rw [← add_mul, ha]
  ring

/-- No nonzero coarse jet vector is annihilated by every even-site source. -/
theorem response_pos (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ j ∈ range n, b j * response y j := by
  have hp := energy_pos_of_average_ne_zero n y b hleft havg hne
  have he := response_energy n y b hleft hright havg hstat
  linarith

/-- A single source site already suffices; no bound between different jets is needed. -/
theorem exists_response_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    ∃ j < n, response y j ≠ 0 := by
  by_contra h
  push Not at h
  have hp := response_pos n y b hleft hright havg hstat hne
  have hz : (∑ j ∈ range n, b j * response y j) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [h j (mem_range.mp hj), mul_zero]
  linarith

/-- Abstract dictionary interface. The actual equality with the source pairing is
separate from the finite-chain theorem, so it cannot silently discharge the dictionary. -/
theorem exists_coupling_ne_zero (n : ℕ) (y b coupling : ℕ → ℝ) (factor : ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0)
    (hfactor : factor ≠ 0)
    (hdict : ∀ j < n, coupling j = factor * response y j) :
    ∃ j < n, coupling j ≠ 0 := by
  obtain ⟨j, hj, hn⟩ := exists_response_ne_zero n y b hleft hright havg hstat hne
  refine ⟨j, hj, ?_⟩
  rw [hdict j hj]
  exact mul_ne_zero hfactor hn

#print axioms lap
#print axioms energy
#print axioms energy_nonneg
#print axioms energy_identity
#print axioms eq_zero_of_energy_zero
#print axioms energy_pos_of_average_ne_zero
#print axioms sum_pair
#print axioms Stationary
#print axioms response
#print axioms response_energy
#print axioms response_pos
#print axioms exists_response_ne_zero
#print axioms exists_coupling_ne_zero

end AdalyFormal.Round10.Nonvanishing.FreeProfile
