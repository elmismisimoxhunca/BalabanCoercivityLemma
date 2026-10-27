import CvK1

/-!
# CvK2 -- the Euler-Lagrange operator of the constrained chain form (lane cover_jacobi_20261016)

* `nx e` : the NEUMANN extension of `e : Fin n -> R` to `Z` (`nx e (-1) = nx e 0`, `nx e n = nx e (n-1)`, clamp otherwise).
* `Wt C c y` : the weight of the edge `(y, y+1)`: `c` for `y in {C-1, C}`, `1` otherwise.
* `BF_single`: for `1 <= C`, `C + 1 < n` and any slice `x`:
  `BF C c e (delta_x) = Wt(x-1) (nx e x - nx e (x-1)) - Wt(x) (nx e (x+1) - nx e x)`,
  i.e. `(L e)_x`, the discrete weighted Laplacian with free (Neumann) ends.
Together with `chain_mult_const` (CvK1) this says: the radical vector of the constrained form satisfies the row-constant Euler-Lagrange identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

variable {n : ℕ}

/-- Neumann extension of `e` to `Z`. -/
noncomputable def nx (e : Fin n → ℝ) (x : ℤ) : ℝ :=
  if h : 0 < n then e ⟨(max 0 (min x ((n : ℤ) - 1))).toNat, by omega⟩ else 0

theorem nx_nat (e : Fin n → ℝ) (k : ℕ) (hk : k < n) : nx e (k : ℤ) = e ⟨k, hk⟩ := by
  have hn : 0 < n := by omega
  unfold nx
  rw [dif_pos hn]
  congr 1
  apply Fin.ext
  simp only []
  omega

theorem nx_neg_one (e : Fin n → ℝ) (hn : 0 < n) : nx e (-1) = nx e 0 := by
  unfold nx
  rw [dif_pos hn, dif_pos hn]
  congr 1
  apply Fin.ext
  simp only []
  omega

theorem nx_n (e : Fin n → ℝ) (hn : 0 < n) : nx e (n : ℤ) = nx e ((n : ℤ) - 1) := by
  unfold nx
  rw [dif_pos hn, dif_pos hn]
  congr 1
  apply Fin.ext
  simp only []
  omega

/-- the weight of the edge `(y, y+1)`. -/
noncomputable def Wt (C : ℕ) (c : ℝ) (y : ℤ) : ℝ := if y = (C : ℤ) - 1 ∨ y = (C : ℤ) then c else 1

theorem ex_single (x : Fin n) (z : ℕ) : ex (Pi.single x (1 : ℝ) : Fin n → ℝ) z = if z = x.val then 1 else 0 := by
  unfold ex
  by_cases hz : z < n
  · rw [dif_pos hz]
    by_cases hzx : z = x.val
    · have : (⟨z, hz⟩ : Fin n) = x := Fin.ext hzx
      rw [this]; simp [hzx]
    · have : (⟨z, hz⟩ : Fin n) ≠ x := fun h => hzx (congrArg Fin.val h)
      simp [Pi.single_apply, this, hzx]
  · rw [dif_neg hz]
    have : z ≠ x.val := by have := x.2; omega
    simp [this]

theorem dlt_single (x : Fin n) (y : ℕ) :
    dlt (Pi.single x (1 : ℝ) : Fin n → ℝ) y = (if y + 1 = x.val then 1 else 0) - (if y = x.val then 1 else 0) := by
  unfold dlt
  rw [ex_single, ex_single]

theorem Wt_eq (C : ℕ) (c : ℝ) (y : ℕ) :
    Wt C c (y : ℤ) = 1 - (1 - c) * (if y + 1 = C then 1 else 0) - (1 - c) * (if y = C then 1 else 0) := by
  unfold Wt
  by_cases h1 : y + 1 = C
  · have h2 : y ≠ C := by omega
    have h1' : (y : ℤ) = (C : ℤ) - 1 := by omega
    simp [h1, h2, h1']
  · by_cases h2 : y = C
    · have h2' : (y : ℤ) = (C : ℤ) := by omega
      have h1'' : ¬ ((y : ℤ) = (C : ℤ) - 1) := by omega
      simp [h1, h2, h2', h1'']
    · have h1'' : ¬ ((y : ℤ) = (C : ℤ) - 1) := by omega
      have h2'' : ¬ ((y : ℤ) = (C : ℤ)) := by omega
      simp [h1, h2, h1'', h2'']

theorem BF_eq_sum (C : ℕ) (c : ℝ) (hC1 : 1 ≤ C) (hC2 : C + 1 < n) (e f : Fin n → ℝ) :
    BF C c e f = ∑ y ∈ range (n - 1), Wt C c (y : ℤ) * (dlt e y * dlt f y) := by
  unfold BF
  have hexp : ∀ y ∈ range (n - 1), Wt C c (y : ℤ) * (dlt e y * dlt f y) =
      dlt e y * dlt f y - (1 - c) * ((if y + 1 = C then 1 else 0) * (dlt e y * dlt f y))
        - (1 - c) * ((if y = C then 1 else 0) * (dlt e y * dlt f y)) := by
    intro y _
    rw [Wt_eq]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ y ∈ range (n - 1), (if y + 1 = C then (1 : ℝ) else 0) * (dlt e y * dlt f y) = dlt e (C - 1) * dlt f (C - 1) := by
    have : ∀ y ∈ range (n - 1), (if y + 1 = C then (1 : ℝ) else 0) * (dlt e y * dlt f y) =
        if y = C - 1 then dlt e (C - 1) * dlt f (C - 1) else 0 := by
      intro y _
      by_cases h : y + 1 = C
      · have : y = C - 1 := by omega
        rw [if_pos h, if_pos this, this]; ring
      · have : y ≠ C - 1 := by omega
        rw [if_neg h, if_neg this]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_pos (by omega)]
  have h2 : ∑ y ∈ range (n - 1), (if y = C then (1 : ℝ) else 0) * (dlt e y * dlt f y) = dlt e C * dlt f C := by
    have : ∀ y ∈ range (n - 1), (if y = C then (1 : ℝ) else 0) * (dlt e y * dlt f y) =
        if y = C then dlt e C * dlt f C else 0 := by
      intro y _
      by_cases h : y = C
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_pos (by omega)]
  rw [h1, h2]
  ring

theorem dlt_nx (e : Fin n → ℝ) (y : ℕ) (hy : y + 1 < n) : dlt e y = nx e ((y : ℤ) + 1) - nx e (y : ℤ) := by
  have h1 : nx e ((y : ℤ) + 1) = e ⟨y + 1, hy⟩ := by
    have := nx_nat e (y + 1) hy
    push_cast at this; exact this
  have h2 : nx e (y : ℤ) = e ⟨y, by omega⟩ := nx_nat e y (by omega)
  rw [h1, h2]
  unfold dlt ex
  rw [dif_pos hy, dif_pos (by omega : y < n)]

theorem sum_shift (h : ℕ → ℝ) (x : ℕ) (hx : x < n) :
    ∑ y ∈ range (n - 1), (if y + 1 = x then h y else 0) = if 1 ≤ x then h (x - 1) else 0 := by
  by_cases h1 : 1 ≤ x
  · have : ∀ y ∈ range (n - 1), (if y + 1 = x then h y else 0) = if y = x - 1 then h (x - 1) else 0 := by
      intro y _
      by_cases hy : y + 1 = x
      · have : y = x - 1 := by omega
        rw [if_pos hy, if_pos this, this]
      · have : y ≠ x - 1 := by omega
        rw [if_neg hy, if_neg this]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_pos (by omega), if_pos h1]
  · have hx0 : x = 0 := by omega
    subst hx0
    simp

theorem sum_pt (h : ℕ → ℝ) (x : ℕ) :
    ∑ y ∈ range (n - 1), (if y = x then h y else 0) = if x < n - 1 then h x else 0 := by
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- the Euler-Lagrange operator of the constrained chain form. -/
theorem BF_single (C : ℕ) (c : ℝ) (hC1 : 1 ≤ C) (hC2 : C + 1 < n) (e : Fin n → ℝ) (x : Fin n) :
    BF C c e (Pi.single x 1) =
      Wt C c ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) -
        Wt C c (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
  rw [BF_eq_sum C c hC1 hC2]
  have hn : 0 < n := by have := x.2; omega
  have hterm : ∀ y ∈ range (n - 1), Wt C c (y : ℤ) * (dlt e y * dlt (Pi.single x (1 : ℝ) : Fin n → ℝ) y) =
      (if y + 1 = x.val then Wt C c (y : ℤ) * dlt e y else 0) - (if y = x.val then Wt C c (y : ℤ) * dlt e y else 0) := by
    intro y _
    rw [dlt_single]
    by_cases h1 : y + 1 = x.val <;> by_cases h2 : y = x.val <;> simp [h1, h2] <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    sum_shift (fun y => Wt C c (y : ℤ) * dlt e y) x.val x.2, sum_pt (fun y => Wt C c (y : ℤ) * dlt e y) x.val]
  have hk := x.2
  -- the two boundary cases handled by the Neumann extension
  have t1 : (if 1 ≤ x.val then Wt C c ((x.val - 1 : ℕ) : ℤ) * dlt e (x.val - 1) else 0) =
      Wt C c ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) := by
    by_cases h1 : 1 ≤ x.val
    · rw [if_pos h1]
      have e1 : ((x.val - 1 : ℕ) : ℤ) = (x.val : ℤ) - 1 := by omega
      have e2 : ((x.val - 1 : ℕ) : ℤ) + 1 = (x.val : ℤ) := by omega
      rw [dlt_nx e (x.val - 1) (by omega), e2, e1]
    · have h0 : x.val = 0 := by omega
      rw [if_neg h1, h0]
      have : nx e ((0 : ℕ) : ℤ) - nx e (((0 : ℕ) : ℤ) - 1) = 0 := by
        have := nx_neg_one e hn
        simp only [Nat.cast_zero, zero_sub] 
        rw [this]; simp
      rw [this]; ring
  have t2 : (if x.val < n - 1 then Wt C c (x.val : ℤ) * dlt e x.val else 0) =
      Wt C c (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
    by_cases h1 : x.val < n - 1
    · rw [if_pos h1, dlt_nx e x.val (by omega)]
    · have h2 : x.val = n - 1 := by omega
      rw [if_neg h1]
      have : nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ) = 0 := by
        have e1 : (x.val : ℤ) + 1 = (n : ℤ) := by omega
        have e2 : (x.val : ℤ) = (n : ℤ) - 1 := by omega
        rw [e1, nx_n e hn, ← e2]; ring
      rw [this]; ring
  rw [t1, t2]


#print axioms nx
#print axioms nx_nat
#print axioms nx_neg_one
#print axioms nx_n
#print axioms Wt
#print axioms ex_single
#print axioms dlt_single
#print axioms Wt_eq
#print axioms BF_eq_sum
#print axioms dlt_nx
#print axioms sum_shift
#print axioms sum_pt
#print axioms BF_single

end AdalyFormal.CoverJacobi
