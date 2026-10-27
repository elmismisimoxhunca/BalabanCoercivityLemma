import NsCvOK4
import CvK6
import CvK7
import NsCvK8

/-!
# CvOK5 -- `qF 0 = 0` forces zero, `e1vec` lies in the constraint space, for the relaxed row geometry (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

theorem qF_zero_eq_zeroD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {i0 : ℕ} (hi01 : 1 ≤ i0) (hi0 : i0 + 1 < R) (hai : a ≤ i0) (hi0b : i0 + b < R) (hC : st i0 = C)
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
  have hrow0 := rowSum_of_memD g he (show 0 < R by omega)
  have h00 : nx e 0 = 0 := by
    unfold BlockSums at hrow0
    have hl0 : ln 0 ≤ C := by
      have h1 := st_monoD g (show 1 ≤ i0 by omega)
      have h2 : st 1 = ln 0 := by have := g.stS 0; simpa [g.st0] using this
      omega
    have hln : 0 < ln 0 := by have := g.ln1 0 (by omega); omega
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
  have hrowR := rowSum_of_memD g he hi0
  have hgam : nx e ((C + 1 : ℕ) : ℤ) = 0 := by
    unfold BlockSums at hrowR
    have hs : st (i0 + 1) = C + ln i0 := by rw [g.stS, hC]
    have hL := g.lnI i0 hai hi0b
    have hL3 := g.ln1 (i0 + 1) hi0
    have hle := row_lt_nD g hi0
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
  have hrowC := rowSum_of_memD g he (show i0 < R by omega)
  have hCz : nx e (C : ℤ) = 0 := by
    unfold BlockSums at hrowC
    have hL := g.lnI i0 hai hi0b
    have hle := row_lt_nD g (show i0 < R by omega)
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



theorem e1vec_memD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {i0 K k r : ℕ}
    (hi0 : i0 < R) (hC : st i0 = K + 1) (hL : ln i0 = k + 3) (hn : n = (K + 1) + (k + 3) + r) :
    e1vec (K + 1) (k + 3) n ∈ Vsub rowOf := by
  intro rr
  by_cases hrr : rr = i0
  · subst hrr
    rw [filter_sum_rowD g hi0]
    have hle := row_lt_nD g hi0
    have hterm : ∀ j : Fin (ln rr), e1vec (K + 1) (k + 3) n ⟨st rr + j.val, by have := j.2; omega⟩ =
        locVec (k + 2) (k + 2 - j.val) := by
      intro j
      have hj := j.2
      unfold e1vec
      rw [if_pos (by simp only []; omega)]
      simp only []
      rw [show k + 3 - 1 = k + 2 by omega, show K + 1 + (k + 3) - 1 - (st rr + j.val) = k + 2 - j.val by omega]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [Fin.sum_univ_eq_sum_range (fun j => locVec (k + 2) (k + 2 - j)) (ln rr), hL]
    have := Finset.sum_range_reflect (fun j => locVec (k + 2) j) (k + 3)
    rw [show k + 3 - 1 = k + 2 by omega] at this
    rw [show ∑ j ∈ Finset.range (k + 3), locVec (k + 2) (k + 2 - j) = ∑ j ∈ Finset.range (k + 3), locVec (k + 2) j from this]
    exact locVec_sum (k + 2)
  · apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    unfold e1vec
    rw [if_neg]
    intro hcond
    have hle := row_lt_nD g hi0
    have := (g.row i0 hi0 x.val x.2).mpr ⟨by omega, by omega⟩
    exact hrr (hx.symm.trans this)


#print axioms qF_zero_eq_zeroD
#print axioms e1vec_memD

end AdalyFormal.CoverOmega
