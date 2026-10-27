import CvK4

/-!
# CvK6 -- the form at the junk point `c = 0` is positive definite on the constraint space (lane cover_jacobi_20261016)

`qF_zero_eq_zero`: if `e` is in the constraint space and `qF C 0 e = 0` then `e = 0`.  (At `c = 0` the layer edges `(C-1,C)`, `(C,C+1)` carry weight 0: the slice `C` is isolated,
the left part `[0, C)` is killed by row `0`, the right part `[C+1, n)` by row `i0 + 1`, the slice `C` by row `i0`.)  Hence the first crossing `c*` of CvK1 is never `0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

variable {n : ℕ}

theorem qF_eq_sum (C : ℕ) (c : ℝ) (hC1 : 1 ≤ C) (hC2 : C + 1 < n) (e : Fin n → ℝ) :
    qF C c e = ∑ y ∈ range (n - 1), Wt C c (y : ℤ) * (dlt e y * dlt e y) := by
  rw [← BF_eq_sum C c hC1 hC2]
  unfold qF BF aF bF
  have : ∑ y ∈ range (n - 1), dlt e y * dlt e y = ∑ y ∈ range (n - 1), (dlt e y) ^ 2 :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem dlt_zero_of_qF_zero (C : ℕ) (hC1 : 1 ≤ C) (hC2 : C + 1 < n) (e : Fin n → ℝ) (hq : qF C 0 e = 0)
    (y : ℕ) (hy : y < n - 1) (h1 : y ≠ C - 1) (h2 : y ≠ C) : dlt e y = 0 := by
  rw [qF_eq_sum C 0 hC1 hC2] at hq
  have hnn : ∀ y ∈ range (n - 1), 0 ≤ Wt C 0 (y : ℤ) * (dlt e y * dlt e y) := by
    intro y _
    unfold Wt
    split_ifs
    · simp
    · simpa using mul_self_nonneg (dlt e y)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hq y (Finset.mem_range.mpr hy)
  have hW : Wt C 0 (y : ℤ) = 1 := by
    unfold Wt; rw [if_neg]; omega
  rw [hW, one_mul] at this
  exact mul_self_eq_zero.mp this

theorem qF_zero_eq_zero {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeom n R st ln rowOf) (C : ℕ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {i0 : ℕ} (hi01 : 1 ≤ i0) (hi0 : i0 + 1 < R) (hC : st i0 = C)
    {e : Fin n → ℝ} (he : e ∈ Vsub rowOf) (hq : qF C 0 e = 0) : e = 0 := by
  have hdl := dlt_zero_of_qF_zero C hC1 hC2 e hq
  have hstep : ∀ y, y + 1 < n → y ≠ C - 1 → y ≠ C → nx e ((y : ℤ) + 1) = nx e (y : ℤ) := by
    intro y hy h1 h2
    have := hdl y (by omega) h1 h2
    rw [dlt_nx e y hy] at this
    linarith
  have hleft : ∀ x, x < C → nx e (x : ℤ) = nx e 0 := by
    intro x
    induction x with
    | zero => intro _; simp
    | succ x ih =>
      intro hx
      have h := hstep x (by omega) (by omega) (by omega)
      have e1 : ((x + 1 : ℕ) : ℤ) = (x : ℤ) + 1 := by push_cast; ring
      rw [e1, h]; exact ih (by omega)
  have hright : ∀ d, C + 1 + d < n → nx e ((C + 1 + d : ℕ) : ℤ) = nx e ((C + 1 : ℕ) : ℤ) := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have h := hstep (C + 1 + d) (by omega) (by omega) (by omega)
      have e1 : ((C + 1 + (d + 1) : ℕ) : ℤ) = ((C + 1 + d : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [e1, h]; exact ih (by omega)
  have hrow0 := rowSum_of_mem g he (show 0 < R by omega)
  have h00 : nx e 0 = 0 := by
    unfold BlockSums at hrow0
    have hl0 : ln 0 ≤ C := by
      have h1 := st_mono g (show 1 ≤ i0 by omega)
      have h2 : st 1 = ln 0 := by have := g.stS 0; simpa [g.st0] using this
      omega
    have hln : 0 < ln 0 := by have := g.ln2 0 (by omega); omega
    have : ∀ j ∈ Finset.range (ln 0), nx e ((st 0 : ℤ) + (j : ℤ)) = nx e 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [g.st0]
      have := hleft j (by omega)
      simpa using this
    rw [Finset.sum_congr rfl this] at hrow0
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hrow0
    have hne : (ln 0 : ℝ) ≠ 0 := by exact_mod_cast hln.ne'
    exact (mul_eq_zero.mp hrow0).resolve_left hne
  have hrowR := rowSum_of_mem g he hi0
  have hgam : nx e ((C + 1 : ℕ) : ℤ) = 0 := by
    unfold BlockSums at hrowR
    have hs : st (i0 + 1) = C + ln i0 := by rw [g.stS, hC]
    have hL := g.ln2 i0 (by omega)
    have hL3 := g.ln2 (i0 + 1) hi0
    have hle := row_lt_n g hi0
    have : ∀ j ∈ Finset.range (ln (i0 + 1)), nx e ((st (i0 + 1) : ℤ) + (j : ℤ)) = nx e ((C + 1 : ℕ) : ℤ) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have := hright (st (i0 + 1) + j - (C + 1)) (by omega)
      have e1 : C + 1 + (st (i0 + 1) + j - (C + 1)) = st (i0 + 1) + j := by omega
      rw [e1] at this
      push_cast at this ⊢
      exact this
    rw [Finset.sum_congr rfl this] at hrowR
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hrowR
    have hne : (ln (i0 + 1) : ℝ) ≠ 0 := by exact_mod_cast (show ln (i0 + 1) ≠ 0 by omega)
    exact (mul_eq_zero.mp hrowR).resolve_left hne
  have hrowC := rowSum_of_mem g he (show i0 < R by omega)
  have hCz : nx e (C : ℤ) = 0 := by
    unfold BlockSums at hrowC
    have hL := g.ln2 i0 (by omega)
    have hle := row_lt_n g (show i0 < R by omega)
    rw [hC] at hrowC
    obtain ⟨L', hL'⟩ : ∃ L', ln i0 = L' + 1 := ⟨ln i0 - 1, by omega⟩
    rw [hL', Finset.sum_range_succ'] at hrowC
    have : ∀ j ∈ Finset.range L', nx e ((C : ℤ) + ((j + 1 : ℕ) : ℤ)) = 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have h := hright j (by omega)
      have e1 : (C : ℤ) + ((j + 1 : ℕ) : ℤ) = ((C + 1 + j : ℕ) : ℤ) := by push_cast; ring
      rw [e1, h, hgam]
    rw [Finset.sum_congr rfl this] at hrowC
    simpa using hrowC
  funext x
  have hx := x.2
  have hxv : nx e (x.val : ℤ) = 0 := by
    rcases lt_trichotomy x.val C with h | h | h
    · rw [hleft x.val h, h00]
    · rw [h]; exact hCz
    · have := hright (x.val - (C + 1)) (by omega)
      have e1 : C + 1 + (x.val - (C + 1)) = x.val := by omega
      rw [e1] at this
      rw [this, hgam]
  have := nx_nat e x.val x.2
  rw [this] at hxv
  simpa using hxv


#print axioms qF_eq_sum
#print axioms dlt_zero_of_qF_zero
#print axioms qF_zero_eq_zero

end AdalyFormal.CoverJacobi
