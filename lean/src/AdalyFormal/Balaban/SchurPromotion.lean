/-
# Promoting the Schur test from a sum inequality to a `ContinuousLinearMap` operator-norm bound.

LANE `compute/thm315_core/`.  Write scope: `compute/thm315_core/` only.

## Why this file exists (OPS-10: close residuals the lane can close)

The sibling lane `compute/p429_pivot/` proved `P429Pivot.schur_test`
(`compute/p429_pivot/staging/SchurStep.lean`) in SUM form,
`∑_y (∑_{y'} K y y' x y')² ≤ S² ∑_y (x y)²`, and listed as still-open:

> "WHAT IS STILL NOT PROVED HERE: Theorem 3.15 itself; the volume-independence of `S`; and the
>  **promotion of `schur_test`'s sum-form to a `ContinuousLinearMap` operator norm**."
> (`compute/p429_pivot/FINDINGS.md`)

This file closes the third of those three.  It builds the integral operator of a kernel `K` as
an honest `ContinuousLinearMap` on `EuclideanSpace ℝ ι` and proves `‖kernelOp K‖ ≤ S` from the
hypotheses of the Schur test.  That is exactly the input
`P429Pivot.coercive_of_inverse_opNorm_le` requires.

The other two residuals in that list are NOT closed here: the volume-independence of `S` is the
deferred quantitative input of the reduction (`Reduction.lean`), and Theorem 3.15 itself is not
proved anywhere in this campaign.

## A defect found while building this, and fixed here

`0 ≤ S` must be a hypothesis of the operator-norm form, and it is NOT derivable from the Schur
hypotheses.  `P429Pivot.schur_test`'s own hypotheses give `0 ≤ S` only when `ι` is nonempty (it
derives it from `hrow` at an arbitrary index); when `ι` is empty, `hrow` is vacuous, `S` may be
negative, and `‖kernelOp K‖ ≤ S` is then FALSE because the left side is `0`.  `schur_test`
itself is unaffected — its conclusion `0 ≤ S² · 0` is true for negative `S` too — but the
operator-norm promotion is not.  `hS : 0 ≤ S` is therefore carried explicitly below, and
`schur_S_nonneg` records that it is free whenever `ι` is nonempty.
-/
import Mathlib
import AdalyFormal.Balaban.SchurStep

namespace Thm315Core

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integral operator of a kernel `K`, as a `ContinuousLinearMap` on `EuclideanSpace ℝ ι`.

Built from Mathlib's `Matrix.toEuclideanLin` (LAW-19: reuse the machinery).  Continuity is
automatic: `EuclideanSpace ℝ ι` is finite dimensional. -/
noncomputable def kernelOp (K : ι → ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.of K))

@[simp] theorem kernelOp_apply (K : ι → ι → ℝ) (x : EuclideanSpace ℝ ι) (y : ι) :
    kernelOp K x y = ∑ y', K y y' * x y' := by
  simp [kernelOp, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct]

/-- The squared Euclidean norm as a plain sum of squares. -/
theorem euclidean_norm_sq (x : EuclideanSpace ℝ ι) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- When `ι` is nonempty, the Schur hypotheses already force `0 ≤ S`. -/
theorem schur_S_nonneg [Nonempty ι] (w : ι → ι → ℝ) (S : ℝ)
    (hw : ∀ y y', 0 ≤ w y y') (hrow : ∀ y, ∑ y', w y y' ≤ S) : 0 ≤ S :=
  le_trans (Finset.sum_nonneg fun i _ => hw (Classical.arbitrary ι) i)
    (hrow (Classical.arbitrary ι))

/-- **Pointwise form of the Schur bound.**  Under the hypotheses of `P429Pivot.schur_test`,
`‖(kernelOp K) x‖ ≤ S * ‖x‖` for every `x`. -/
theorem norm_kernelOp_apply_le (K w : ι → ι → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hw : ∀ y y', 0 ≤ w y y')
    (hK : ∀ y y', |K y y'| ≤ w y y')
    (hsymm : ∀ y y', w y y' = w y' y)
    (hrow : ∀ y, ∑ y', w y y' ≤ S)
    (x : EuclideanSpace ℝ ι) :
    ‖kernelOp K x‖ ≤ S * ‖x‖ := by
  have hsum := P429Pivot.schur_test K w S hw hK hsymm hrow (fun i => x i)
  have hlhs : ‖kernelOp K x‖ ^ 2 = ∑ y, (∑ y', K y y' * x y') ^ 2 := by
    rw [euclidean_norm_sq]
    simp only [kernelOp_apply]
  have hrhs : ‖x‖ ^ 2 = ∑ y, (x y) ^ 2 := euclidean_norm_sq x
  have hsq : ‖kernelOp K x‖ ^ 2 ≤ (S * ‖x‖) ^ 2 := by
    rw [hlhs, mul_pow, hrhs]; exact hsum
  nlinarith [hsq, norm_nonneg (kernelOp K x), mul_nonneg hS (norm_nonneg x)]

/-- **THE PROMOTION.**  Under the hypotheses of `P429Pivot.schur_test` together with `0 ≤ S`,
the operator norm of the kernel operator is at most the Schur constant: `‖kernelOp K‖ ≤ S`.

This is the missing link between `P429Pivot.schur_test` (a sum inequality) and
`P429Pivot.coercive_of_inverse_opNorm_le` (which consumes `‖M‖ ≤ B`). -/
theorem opNorm_kernelOp_le (K w : ι → ι → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hw : ∀ y y', 0 ≤ w y y')
    (hK : ∀ y y', |K y y'| ≤ w y y')
    (hsymm : ∀ y y', w y y' = w y' y)
    (hrow : ∀ y, ∑ y', w y y' ≤ S) :
    ‖kernelOp K‖ ≤ S :=
  ContinuousLinearMap.opNorm_le_bound _ hS
    (fun x => norm_kernelOp_apply_le K w S hS hw hK hsymm hrow x)

/-- **MUST-FIRE CONTROL for `opNorm_kernelOp_le`.**  The bound is attained, so `S` cannot be
replaced by anything smaller in general: for the identity kernel on a one-point index set, the
Schur hypotheses hold with `S = 1` and the operator norm is exactly `1`.  In particular the
conclusion is not the vacuous `‖·‖ ≤ ∞`. -/
theorem opNorm_kernelOp_sharp :
    kernelOp (ι := Fin 1) (fun _ _ => (1:ℝ)) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  ext x i
  simp [Fin.fin_one_eq_zero i]

end Thm315Core
