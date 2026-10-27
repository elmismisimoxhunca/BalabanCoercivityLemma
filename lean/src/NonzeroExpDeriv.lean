/-
Owned SI1 phi-2 scratch file (compute/m1_si1_phi2/exp/). Imports the frozen `AdalyFormal`
package read-only; does not modify it.

## Scope of this pass

The banked `hasDerivAt_su2Exp_coe_smul` (compute/m1_si1_deriv/diff/IngredientDeriv.lean) only
covers `t ↦ exp(t•H)` THROUGH THE ORIGIN: basepoint `X = 0`. This file supplies the first owed
object named in HANDOFF.md / COORDINATOR_REVIEW.md: a genuine derivative of `su2Exp`/matrix `exp`
at a NONZERO Lie-algebra basepoint `X`, in an arbitrary tangent direction `H` (not required to
commute with `X`, not required to be proportional to it) — `d/dt|0 exp(X + t•H) = Dexp(X)[H]`.

**Route reused from Mathlib, no new analysis derived.** `NormedSpace.exp_analytic` establishes
`AnalyticAt 𝕂 NormedSpace.exp x` at EVERY point `x` of EVERY complete normed algebra, with no
commutativity hypothesis (`section AnyAlgebra` in `Mathlib.Analysis.Normed.Algebra.Exponential`,
in contrast to the commutative-only `hasFDerivAt_exp_of_mem_ball`). Composing the resulting
`HasFDerivAt NormedSpace.exp (fderiv ℝ NormedSpace.exp X) X` with the affine chart curve
`t ↦ X + t•H` via the ordinary chain rule (`HasFDerivAt.comp_hasDerivAt`) gives exactly the
requested `HasDerivAt` at `t = 0`, with `Dexp(X)[H] := (fderiv ℝ NormedSpace.exp X) H` the genuine
(possibly non-closed-form, but honest) noncommutative Fréchet derivative — not a value identity,
not a gradient, not a forced equality. Transport to `su2Exp` reuses the SAME guard-discharge lemma
`su2Exp_coe_of_antiHerm_traceless` the origin case used, applied along the whole chart curve (valid
for every real `t`, since su(2) exponentiates onto all of SU(2) unconditionally — no radius bound
needed, unlike `EndpointChartMargin`).
-/
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp

set_option autoImplicit false

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.NonzeroExpDeriv

open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Exp_coe_of_antiHerm_traceless)

/-! ## The chart neighborhood: `X + t•H` stays traceless anti-Hermitian for every real `t`

Both hypotheses are stated on `X` AND `H` separately (mirroring the origin-case
`smul_conjTranspose_eq_neg`/`smul_trace_eq_zero` of `IngredientDeriv.lean`), since `su(2)` is a
real-linear subspace of `M2`: the sum of two traceless anti-Hermitian matrices is traceless
anti-Hermitian, and this holds for the WHOLE real line in `t`, not merely a neighborhood of `0`. -/

theorem add_smul_conjTranspose_eq_neg {X H : M2} (hX : Xᴴ = -X) (hH : Hᴴ = -H) (t : ℝ) :
    (X + t • H)ᴴ = -(X + t • H) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX, hH]
  simp only [smul_neg, star_trivial]
  abel

theorem add_smul_trace_eq_zero {X H : M2} (htX : Matrix.trace X = 0) (htH : Matrix.trace H = 0)
    (t : ℝ) : Matrix.trace (X + t • H) = 0 := by
  rw [Matrix.trace_add, Matrix.trace_smul, htX, htH, smul_zero, add_zero]

theorem su2Exp_coe_add_smul_eq {X H : M2} (hX : Xᴴ = -X) (hH : Hᴴ = -H)
    (htX : Matrix.trace X = 0) (htH : Matrix.trace H = 0) (t : ℝ) :
    ((su2Exp (X + t • H) : SU2) : M2) = NormedSpace.exp (X + t • H) :=
  su2Exp_coe_of_antiHerm_traceless (add_smul_conjTranspose_eq_neg hX hH t)
    (add_smul_trace_eq_zero htX htH t)

#print axioms add_smul_conjTranspose_eq_neg
#print axioms add_smul_trace_eq_zero
#print axioms su2Exp_coe_add_smul_eq

/-- **PAID — `su2Exp`/matrix `exp`, at a NONZERO Lie-algebra basepoint `X`, arbitrary direction
`H`.** For ARBITRARY traceless anti-Hermitian `X` (not fixed to `0`) and ARBITRARY traceless
anti-Hermitian `H` (not required to commute with `X`), the chart curve
`t ↦ ((su2Exp (X + t•H) : SU2) : M2)` has derivative exactly `(fderiv ℝ NormedSpace.exp X) H` at
`t = 0` — the genuine noncommutative Fréchet derivative coefficient of the ambient matrix
exponential at `X`, evaluated in direction `H`. Not merely `t ↦ exp(t•H)` through the origin. -/
theorem hasDerivAt_su2Exp_coe_add_smul {X H : M2} (hX : Xᴴ = -X) (hH : Hᴴ = -H)
    (htX : Matrix.trace X = 0) (htH : Matrix.trace H = 0) :
    HasDerivAt (fun t : ℝ => ((su2Exp (X + t • H) : SU2) : M2))
      ((fderiv ℝ NormedSpace.exp X) H) 0 := by
  have hanalytic : AnalyticAt ℝ NormedSpace.exp X :=
    NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) X
  have hfd := hanalytic.differentiableAt.hasFDerivAt
  have haffine0 := (hasDerivAt_id (0 : ℝ)).smul_const H
  simp only [one_smul] at haffine0
  have haffine := haffine0.const_add X
  have hraw := hfd.comp_hasDerivAt_of_eq 0 haffine (by simp)
  exact hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => su2Exp_coe_add_smul_eq hX hH htX htH t))

#print axioms hasDerivAt_su2Exp_coe_add_smul

end AdalySI1.NonzeroExpDeriv
