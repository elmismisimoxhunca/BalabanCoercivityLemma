/-
# The Schur step: a pointwise kernel bound gives an l2 operator bound.

This is the SECOND missing link between CMP99b Theorem 3.15 (p.432) --
`|C^(k)(Λ;y,y')| ≤ B₀ e^(-δ₀|y-y'|)`, `B₀, δ₀` depending on `d` and `L` only --
and CMP99b p.428's `γ₀`.  Composed with `PivotBridge.coercive_of_inverse_opNorm_le`
it gives `γ₀ = 1/S` where `S` is the Schur constant of the kernel bound.

The volume-dependence is deliberately left VISIBLE: `S` is a hypothesis (a uniform bound on
the row sums of the majorant `w`), NOT derived here.  That is the honest interface: on a fixed
finite lattice, `S` always exists (take the actual max), and the CONTENT of Theorem 3.15 is
precisely that `S` can be chosen independent of the lattice extent.  Compare the tree's own
standing gate `AdalyFormal.Assumptions.finite_domain_decay_conclusion_is_free`.

Self-contained: imports Mathlib only.  Write scope: compute/p429_pivot/.
-/
import Mathlib

namespace P429Pivot

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Schur test, symmetric-majorant form.** If `|K y y'| ≤ w y y'` with `w` nonnegative,
symmetric, and every row sum of `w` at most `S`, then the induced operator has `ℓ²` norm at
most `S`:  `∑_y (∑_{y'} K y y' * x y')² ≤ S² * ∑_y (x y)²`. -/
theorem schur_test
    (K w : ι → ι → ℝ) (S : ℝ)
    (hw : ∀ y y', 0 ≤ w y y')
    (hK : ∀ y y', |K y y'| ≤ w y y')
    (hsymm : ∀ y y', w y y' = w y' y)
    (hrow : ∀ y, ∑ y', w y y' ≤ S)
    (x : ι → ℝ) :
    ∑ y, (∑ y', K y y' * x y') ^ 2 ≤ S ^ 2 * ∑ y, (x y) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hemp | hne
  · simp
  have hS : 0 ≤ S :=
    le_trans (Finset.sum_nonneg (fun i _ => hw (Classical.arbitrary ι) i))
      (hrow (Classical.arbitrary ι))
  -- ROW STEP: for each y, the squared entry is bounded by S * (weighted energy)
  have key : ∀ y, (∑ y', K y y' * x y') ^ 2 ≤ S * ∑ y', w y y' * (x y') ^ 2 := by
    intro y
    have habs : |∑ y', K y y' * x y'| ≤ ∑ y', w y y' * |x y'| := by
      calc |∑ y', K y y' * x y'| ≤ ∑ y', |K y y' * x y'| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ y', |K y y'| * |x y'| := by simp [abs_mul]
        _ ≤ ∑ y', w y y' * |x y'| :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hK y i) (abs_nonneg _))
    have hcs : (∑ y', w y y' * |x y'|) ^ 2
        ≤ (∑ y', w y y') * ∑ y', w y y' * (x y') ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
        (fun i _ => hw y i)
        (fun i _ => mul_nonneg (hw y i) (sq_nonneg _))
        (fun i _ => by
          have : (w y i * |x i|) ^ 2 = w y i * (w y i * (x i) ^ 2) := by
            rw [mul_pow, sq_abs]; ring
          exact le_of_eq this)
    have hsq : (∑ y', K y y' * x y') ^ 2 ≤ (∑ y', w y y' * |x y'|) ^ 2 := by
      have hnn : 0 ≤ ∑ y', w y y' * |x y'| :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hw y i) (abs_nonneg _))
      nlinarith [habs, abs_nonneg (∑ y', K y y' * x y'),
        sq_abs (∑ y', K y y' * x y'), hnn]
    have henergy : 0 ≤ ∑ y', w y y' * (x y') ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw y i) (sq_nonneg _))
    calc (∑ y', K y y' * x y') ^ 2 ≤ (∑ y', w y y' * |x y'|) ^ 2 := hsq
      _ ≤ (∑ y', w y y') * ∑ y', w y y' * (x y') ^ 2 := hcs
      _ ≤ S * ∑ y', w y y' * (x y') ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow y) henergy
  -- SUM AND SWAP: symmetry turns row sums into column sums
  calc ∑ y, (∑ y', K y y' * x y') ^ 2
      ≤ ∑ y, S * ∑ y', w y y' * (x y') ^ 2 := Finset.sum_le_sum (fun y _ => key y)
    _ = S * ∑ y, ∑ y', w y y' * (x y') ^ 2 := by rw [Finset.mul_sum]
    _ = S * ∑ y', (∑ y, w y y') * (x y') ^ 2 := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun y' _ => by rw [Finset.sum_mul])
    _ ≤ S * ∑ y', S * (x y') ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y' _ => ?_)) hS
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        calc ∑ y, w y y' = ∑ y, w y' y := Finset.sum_congr rfl (fun y _ => hsymm y y')
          _ ≤ S := hrow y'
    _ = S ^ 2 * ∑ y', (x y') ^ 2 := by rw [← Finset.mul_sum]; ring

/-- **Must-not-fire control.** The Schur constant is genuinely used: at `w ≡ 1` on a type with
`n` elements, `S` must be at least `n`, so the bound `S² ∑x²` is `≥ n² ∑ x²` — it does NOT
collapse to the pointwise bound.  Concretely, the row-sum hypothesis forces `Fintype.card ι ≤ S`
whenever `w ≡ 1`. -/
theorem schur_constant_is_card_when_w_one
    (S : ℝ) (hrow : ∀ _y : ι, (∑ _y' : ι, (1:ℝ)) ≤ S) [Nonempty ι] :
    (Fintype.card ι : ℝ) ≤ S := by
  have := hrow (Classical.arbitrary ι)
  simpa [Finset.sum_const, Finset.card_univ] using this

end P429Pivot
