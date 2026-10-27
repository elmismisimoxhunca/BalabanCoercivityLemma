import CvK2
import CvJ3
import CvJ4
import CvK3

/-!
# CvOK1 -- RELAXED row geometry (end rows may be singletons) and the row-level identities (lane omega)

`RowGeomD n R a b`: like `CoverJacobi.RowGeom` but the first `a` rows and the last `b` rows are singleton (collar) rows, pinned to `0` by their row sums, and all other rows have `ln >= 2`.  Copies of the CvK3 identities for `RowGeomD`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n a b : ℕ}

/-- the relaxed row structure of the chain. -/
structure RowGeomD (n R a b : ℕ) (st ln rowOf : ℕ → ℕ) : Prop where
  st0 : st 0 = 0
  stS : ∀ i, st (i + 1) = st i + ln i
  ln1 : ∀ i, i < R → 1 ≤ ln i
  lnL : ∀ i, i < a → ln i = 1
  lnI : ∀ i, a ≤ i → i + b < R → 2 ≤ ln i
  lnR : ∀ i, R ≤ i + b → i < R → ln i = 1
  stR : st R = n
  row : ∀ i, i < R → ∀ x, x < n → (rowOf x = i ↔ st i ≤ x ∧ x < st i + ln i)
  cover : ∀ x, x < n → ∃ i, i < R ∧ st i ≤ x ∧ x < st i + ln i

theorem st_monoD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {i j : ℕ} (h : i ≤ j) : st i ≤ st j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [g.stS]; omega

theorem row_lt_nD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {i : ℕ} (hi : i < R) :
    st i + ln i ≤ n := by
  have := st_monoD g (show i + 1 ≤ R by omega)
  rw [g.stS, g.stR] at this
  exact this

/-- the filtered sum over a row, as a sum over `Fin (ln i)`. -/
theorem filter_sum_rowD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {i : ℕ} (hi : i < R)
    (f : Fin n → ℝ) :
    ∑ x ∈ (univ.filter (fun x : Fin n => rowOf x.val = i)), f x =
      ∑ j : Fin (ln i), f ⟨st i + j.val, by have := j.2; have := row_lt_nD g hi; omega⟩ := by
  have hle := row_lt_nD g hi
  symm
  refine Finset.sum_bij (fun (j : Fin (ln i)) _ => (⟨st i + j.val, by have := j.2; omega⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro j _
    have hj' := j.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (g.row i hi (st i + j.val) (by omega)).mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    have := congrArg Fin.val hab
    simp only [] at this
    exact Fin.ext (by omega)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := (g.row i hi x.val x.2).mp hx
    refine ⟨⟨x.val - st i, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only []
    omega
  · intro j _
    rfl

/-- the row sum in the form needed by the block lemmas. -/
theorem rowSum_of_memD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) {e : Fin n → ℝ}
    (he : e ∈ Vsub rowOf) {i : ℕ} (hi : i < R) :
    BlockSums (st i : ℤ) (ln i) (nx e) := by
  have hrow := he i
  have hle := row_lt_nD g hi
  unfold BlockSums
  rw [filter_sum_rowD g hi e] at hrow
  rw [← hrow, ← Fin.sum_univ_eq_sum_range (fun j => nx e ((st i : ℤ) + (j : ℤ))) (ln i)]
  apply Finset.sum_congr rfl
  intro j _
  have := nx_nat e (st i + j.val) (by have := j.2; omega)
  push_cast at this
  exact this

/-- the Euler-Lagrange operator is constant along each row. -/
theorem rowEL_rawD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ}
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0) {i : ℕ} (hi : i < R) :
    ∀ j : ℕ, j < ln i →
      Wt C c (((st i + j : ℕ) : ℤ) - 1) * (nx e ((st i + j : ℕ) : ℤ) - nx e (((st i + j : ℕ) : ℤ) - 1)) -
        Wt C c ((st i + j : ℕ) : ℤ) * (nx e (((st i + j : ℕ) : ℤ) + 1) - nx e ((st i + j : ℕ) : ℤ)) = rowMu C c e st i := by
  have hle := row_lt_nD g hi
  have h2 := g.ln1 i hi
  let x0 : Fin n := ⟨st i, by omega⟩
  intro j hj
  let x : Fin n := ⟨st i + j, by omega⟩
  have hx : rowOf x.val = rowOf x0.val := by
    have a := (g.row i hi x.val x.2).mpr ⟨by simp [x], by simp [x]; omega⟩
    have b := (g.row i hi x0.val x0.2).mpr ⟨le_rfl, by simp [x0]; omega⟩
    rw [a, b]
  have := chain_mult_const rowOf C c e hrad x x0 hx
  rw [BF_single C c hC1 hC2 e x] at this
  have hmu : rowMu C c e st i = BF C c e (Pi.single x0 1) := by
    unfold rowMu; rw [dif_pos (by omega)]
  rw [hmu, ← this]

/-- flat rows: the unweighted Euler-Lagrange identity. -/
theorem rowEL_flatD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ}
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0) {i : ℕ} (hi : i < R)
    (hflat : ∀ j : ℕ, j < ln i → st i + j ≠ C - 1 ∧ st i + j ≠ C ∧ st i + j ≠ C + 1) :
    BlockELs (st i : ℤ) (ln i) (nx e) (rowMu C c e st i) := by
  have hμ := rowEL_rawD g C c hC1 hC2 hrad hi
  intro j hj
  have h := hμ j hj
  obtain ⟨a1, a2, a3⟩ := hflat j hj
  have w1 : Wt C c (((st i + j : ℕ) : ℤ) - 1) = 1 := by
    unfold Wt; rw [if_neg]; omega
  have w2 : Wt C c ((st i + j : ℕ) : ℤ) = 1 := by
    unfold Wt; rw [if_neg]; omega
  rw [w1, w2] at h
  push_cast at h
  linarith

/-- the layer row `i0` (`C = st i0`, `ln i0 >= 3`): the weighted identities. -/
theorem rowEL_layerD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ}
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0) {i0 : ℕ} (hi : i0 < R)
    (hC : st i0 = C) (hL : 3 ≤ ln i0) :
    LayerELs (C : ℤ) (ln i0) (nx e) (rowMu C c e st i0) c := by
  have hμ := rowEL_rawD g C c hC1 hC2 hrad hi
  refine ⟨?_, ?_, ?_⟩
  · have h := hμ 0 (by omega)
    rw [hC] at h
    have w1 : Wt C c (((C + 0 : ℕ) : ℤ) - 1) = c := by unfold Wt; rw [if_pos]; left; push_cast; ring
    have w2 : Wt C c ((C + 0 : ℕ) : ℤ) = c := by unfold Wt; rw [if_pos]; right; push_cast; ring
    rw [w1, w2] at h
    push_cast at h
    simpa using h
  · have h := hμ 1 (by omega)
    rw [hC] at h
    have w1 : Wt C c (((C + 1 : ℕ) : ℤ) - 1) = c := by unfold Wt; rw [if_pos]; right; push_cast; ring
    have w2 : Wt C c ((C + 1 : ℕ) : ℤ) = 1 := by unfold Wt; rw [if_neg]; push_cast; omega
    rw [w1, w2] at h
    push_cast at h
    have e1 : (C : ℤ) + 1 + 1 = (C : ℤ) + 2 := by ring
    have e2 : (C : ℤ) + 1 - 1 = (C : ℤ) := by ring
    rw [e1] at h
    rw [e2] at h
    linarith
  · intro j hj2 hjL
    have h := hμ j hjL
    rw [hC] at h
    have w1 : Wt C c (((C + j : ℕ) : ℤ) - 1) = 1 := by unfold Wt; rw [if_neg]; push_cast; omega
    have w2 : Wt C c ((C + j : ℕ) : ℤ) = 1 := by unfold Wt; rw [if_neg]; push_cast; omega
    rw [w1, w2] at h
    push_cast at h
    have e1 : (C : ℤ) + j - 1 = (C : ℤ) + j - 1 := rfl
    linarith

/-- the row before the layer row: flat identities, GIVEN the zero state at the layer cut. -/
theorem rowEL_prevD {R : ℕ} {st ln rowOf : ℕ → ℕ} (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ)
    (hC1 : 1 ≤ C) (hC2 : C + 1 < n) {e : Fin n → ℝ}
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c e d = 0) {i0 : ℕ} (hi : i0 < R) (hi1 : 1 ≤ i0)
    (hC : st i0 = C) (hz : nx e (C : ℤ) = 0 ∧ nx e (C : ℤ) - nx e ((C : ℤ) - 1) = 0) :
    BlockELs (st (i0 - 1) : ℤ) (ln (i0 - 1)) (nx e) (rowMu C c e st (i0 - 1)) := by
  have hi' : i0 - 1 < R := by omega
  have hμ := rowEL_rawD g C c hC1 hC2 hrad hi'
  have hend : st (i0 - 1) + ln (i0 - 1) = C := by
    have := g.stS (i0 - 1)
    have e1 : i0 - 1 + 1 = i0 := by omega
    rw [e1, hC] at this
    omega
  have h2 := g.ln1 (i0 - 1) hi'
  intro j hj
  have h := hμ j hj
  by_cases hlast : j + 1 = ln (i0 - 1)
  · -- last slice of the row: x = C - 1
    have hx : st (i0 - 1) + j = C - 1 := by omega
    rw [hx] at h
    have hC1' : ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by omega
    have w1 : Wt C c (((C - 1 : ℕ) : ℤ) - 1) = 1 := by unfold Wt; rw [if_neg]; omega
    have w2 : Wt C c ((C - 1 : ℕ) : ℤ) = c := by unfold Wt; rw [if_pos]; left; exact hC1'
    rw [w1, w2] at h
    have hxz : ((st (i0 - 1) : ℤ) + (j : ℤ)) = (C : ℤ) - 1 := by
      have : ((st (i0 - 1) + j : ℕ) : ℤ) = ((C - 1 : ℕ) : ℤ) := by rw [hx]
      push_cast at this; omega
    rw [hxz]
    have hd : nx e (C : ℤ) - nx e ((C : ℤ) - 1) = 0 := hz.2
    rw [hC1'] at h
    have e2 : (C : ℤ) - 1 + 1 = (C : ℤ) := by ring
    rw [e2] at h
    rw [e2]
    rw [hd, mul_zero] at h
    linarith
  · have hx1 : st (i0 - 1) + j ≠ C - 1 := by omega
    have hx2 : st (i0 - 1) + j ≠ C := by omega
    have hx3 : st (i0 - 1) + j ≠ C + 1 := by omega
    have w1 : Wt C c (((st (i0 - 1) + j : ℕ) : ℤ) - 1) = 1 := by unfold Wt; rw [if_neg]; push_cast; omega
    have w2 : Wt C c ((st (i0 - 1) + j : ℕ) : ℤ) = 1 := by unfold Wt; rw [if_neg]; push_cast; omega
    rw [w1, w2] at h
    push_cast at h
    linarith



#print axioms rowSum_of_memD
#print axioms rowEL_rawD
#print axioms rowEL_flatD
#print axioms rowEL_layerD
#print axioms rowEL_prevD

end AdalyFormal.CoverOmega
