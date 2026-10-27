import NuC1

/-!
# NuC2 -- the Euler-Lagrange identity of the single-edge chain form and the row multipliers (lane ncwdh_ell2_20261018)

`W1 C c y` is the weight of the edge `(y, y+1)`: `c` for `y = C`, `1` otherwise.
`BF1_single`: `BF1 e δ_x = W1(x-1)(e_x - e_{x-1}) - W1(x)(e_{x+1} - e_x)` (Neumann extension `nx`).
`rowEL_raw1`: for a radical vector the identity takes the same value `rowMu1` on every slice of a row.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega

section chain
variable {n : ℕ}

/-- the weight of the edge `(y, y+1)`: `c` on the single layer edge `y = C`, `1` elsewhere. -/
noncomputable def W1 (C : ℕ) (c : ℝ) (y : ℤ) : ℝ := if y = (C : ℤ) then c else 1

theorem W1_eq (C : ℕ) (c : ℝ) (y : ℕ) : W1 C c (y : ℤ) = 1 - (1 - c) * (if y = C then 1 else 0) := by
  unfold W1
  by_cases h : y = C
  · have h' : (y : ℤ) = (C : ℤ) := by omega
    simp [h, h']
  · have h' : ¬ ((y : ℤ) = (C : ℤ)) := by omega
    simp [h, h']

theorem BF1_eq_sum (C : ℕ) (c : ℝ) (hC : C + 1 < n) (e f : Fin n → ℝ) :
    BF1 C c e f = ∑ y ∈ range (n - 1), W1 C c (y : ℤ) * (dlt e y * dlt f y) := by
  unfold BF1
  have hexp : ∀ y ∈ range (n - 1), W1 C c (y : ℤ) * (dlt e y * dlt f y) =
      dlt e y * dlt f y - (1 - c) * ((if y = C then 1 else 0) * (dlt e y * dlt f y)) := by
    intro y _
    rw [W1_eq]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum]
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
  rw [h2]

/-- the Euler-Lagrange operator of the constrained single-edge chain form. -/
theorem BF1_single (C : ℕ) (c : ℝ) (hC : C + 1 < n) (e : Fin n → ℝ) (x : Fin n) :
    BF1 C c e (Pi.single x 1) =
      W1 C c ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) -
        W1 C c (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
  rw [BF1_eq_sum C c hC]
  have hn : 0 < n := by have := x.2; omega
  have hterm : ∀ y ∈ range (n - 1), W1 C c (y : ℤ) * (dlt e y * dlt (Pi.single x (1 : ℝ) : Fin n → ℝ) y) =
      (if y + 1 = x.val then W1 C c (y : ℤ) * dlt e y else 0) - (if y = x.val then W1 C c (y : ℤ) * dlt e y else 0) := by
    intro y _
    rw [dlt_single]
    by_cases h1 : y + 1 = x.val <;> by_cases h2 : y = x.val <;> simp [h1, h2] <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    sum_shift (fun y => W1 C c (y : ℤ) * dlt e y) x.val x.2, sum_pt (fun y => W1 C c (y : ℤ) * dlt e y) x.val]
  have hk := x.2
  have t1 : (if 1 ≤ x.val then W1 C c ((x.val - 1 : ℕ) : ℤ) * dlt e (x.val - 1) else 0) =
      W1 C c ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) := by
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
  have t2 : (if x.val < n - 1 then W1 C c (x.val : ℤ) * dlt e x.val else 0) =
      W1 C c (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
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

/-- the multiplier of row `i`: `BF1 e δ_{st i}`. -/
noncomputable def rowMu1 (C : ℕ) (c : ℝ) (e : Fin n → ℝ) (st : ℕ → ℕ) (i : ℕ) : ℝ :=
  if h : st i < n then BF1 C c e (Pi.single (⟨st i, h⟩ : Fin n) 1) else 0

/-- the Euler-Lagrange operator is constant along each row. -/
theorem rowEL_raw1 {a b R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC : C + 1 < n) {e : Fin n → ℝ}
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF1 C c e d = 0) {i : ℕ} (hi : i < R) :
    ∀ j : ℕ, j < ln i →
      W1 C c (((st i + j : ℕ) : ℤ) - 1) * (nx e ((st i + j : ℕ) : ℤ) - nx e (((st i + j : ℕ) : ℤ) - 1)) -
        W1 C c ((st i + j : ℕ) : ℤ) * (nx e (((st i + j : ℕ) : ℤ) + 1) - nx e ((st i + j : ℕ) : ℤ)) = rowMu1 C c e st i := by
  have hle := row_lt_nD g hi
  have h2 := g.ln1 i hi
  let x0 : Fin n := ⟨st i, by omega⟩
  intro j hj
  let x : Fin n := ⟨st i + j, by omega⟩
  have hx : rowOf x.val = rowOf x0.val := by
    have a := (g.row i hi x.val x.2).mpr ⟨by simp [x], by simp [x]; omega⟩
    have b := (g.row i hi x0.val x0.2).mpr ⟨le_rfl, by simp [x0]; omega⟩
    rw [a, b]
  have := chain_mult_const1 rowOf C c e hrad x x0 hx
  rw [BF1_single C c hC e x] at this
  have hmu : rowMu1 C c e st i = BF1 C c e (Pi.single x0 1) := by
    unfold rowMu1; rw [dif_pos (by omega)]
  rw [hmu, ← this]

end chain

end AdalyFormal.NcwdhTwo
