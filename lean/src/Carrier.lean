/-
# `Carrier` — the derivation, instantiated at the actual `2×2` algebra, PRINTED CONSTANTS.

LANE `compute/rendering_step_v2/`.  Write scope: that directory only.  Never `lake build`.

**SUPERSEDES `compute/rendering_step/stage/Carrier.lean`.**  The mathematics of the instance
plumbing is carried over unchanged; what changed is the printed size.  That module's
`rendering_step_at_herm2` took

    ha : a ^ 2 = 2 * (x ^ 2 + Complex.normSq y)          -- the UNNORMALIZED trace

and therefore fixed `a = √2·|A|`, making its `hprint` a `√2`-tightening of (3.35).  Here

    ha : a ^ 2 = TwoByTwo.printedNormSq x y = x ^ 2 + Complex.normSq y

is the size CMP99b prints (`|A|² = tr A*A`, `tr 1 = 1`), and `hprint` is (3.35) itself.

`Matrix (Fin 2) (Fin 2) ℂ` with the `l²` operator norm (`scoped[Matrix.Norms.L2Operator]`,
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`) carries every instance `RenderStep` needs; `ℝ`-scalars
come from `NormedAlgebra.restrictScalars ℝ ℂ`, the construction Mathlib itself uses at
`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:374`.

DISCLOSED: this module declares `instNormedAlgebraRealM2` as an `instance`.  A consumer importing
it inherits that `ℝ`-algebra structure on `Matrix (Fin 2) (Fin 2) ℂ`.

Nothing here is graded by this lane (BUILD DISCIPLINE 8); it reports facts.
-/
import Mathlib
import RenderStep
import TwoByTwo

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

namespace Carrier

open scoped Matrix.Norms.L2Operator

/-- The `2×2` complex matrices with the `l²` operator norm — the algebra `SU(2)` acts on. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- `ℝ`-scalars by restriction from `ℂ`. -/
noncomputable instance instNormedAlgebraRealM2 : NormedAlgebra ℝ M2 :=
  NormedAlgebra.restrictScalars ℝ ℂ M2

/-! ## §1 — EVERY INSTANCE HYPOTHESIS OF `RenderStep` IS SATISFIED HERE

These are not `#synth` comments: each is a term whose elaboration IS the check. -/

noncomputable example : NormedRing M2 := inferInstance
noncomputable example : CompleteSpace M2 := inferInstance
noncomputable example : StarRing M2 := inferInstance
noncomputable example : CStarRing M2 := inferInstance
noncomputable example : ContinuousStar M2 := inferInstance
noncomputable example : StarModule ℝ M2 := inferInstance
noncomputable example : Nontrivial M2 := inferInstance
noncomputable example : NormedAlgebra ℝ M2 := inferInstance

/-- The core estimate of `RenderStep` §1.1, instantiated here. -/
theorem core_estimate_at_M2 (X : M2) (C : ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖NormedSpace.exp (t • X)‖ ≤ C) :
    ‖NormedSpace.exp X - 1‖ ≤ C * ‖X‖ :=
  RenderStep.norm_exp_sub_one_le_of_path_bound X C h

/-- The sharp bound of `RenderStep` §1.3, instantiated here. -/
theorem sharp_bound_at_M2 (Y : M2) (hY : star Y = -Y) :
    ‖NormedSpace.exp Y - 1‖ ≤ ‖Y‖ :=
  RenderStep.norm_exp_sub_one_le_of_skewAdjoint hY

/-! ## §2 — THE ALGEBRA IS NONCOMMUTATIVE, AND THE ADJOINT STEP IS NON-TRIVIAL ON IT -/

/-- `σ₃ = diag(1,−1)` is its own two-sided inverse. -/
theorem pauli3_mul_self : TwoByTwo.herm2 1 0 * TwoByTwo.herm2 1 0 = (1 : M2) :=
  TwoByTwo.herm2_sq_pauli3

/-- **NON-VACUITY OF THE ADJOINT STEP.**  `Ad(σ₃)` is NOT the identity on this carrier:
`σ₃σ₁σ₃ = −σ₁`. -/
theorem adOp_nontrivial_at_M2 :
    RenderStep.adOp (TwoByTwo.herm2 1 0) (TwoByTwo.herm2 1 0) (TwoByTwo.herm2 0 1)
      ≠ TwoByTwo.herm2 0 1 := by
  intro h
  rw [RenderStep.adOp_apply] at h
  have h01 : (TwoByTwo.herm2 1 0 * TwoByTwo.herm2 0 1 * TwoByTwo.herm2 1 0) 0 1
      = TwoByTwo.herm2 0 1 0 1 := by rw [h]
  simp [TwoByTwo.herm2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-! ## §3 — THE PRINTED `i`, IN THIS ALGEBRA -/

/-- The printed `i` of `e^{iηA}` as an element of `M2`: `i·1`. -/
noncomputable def imagUnit : M2 := (Complex.I : ℂ) • (1 : M2)

/-- `imagUnit` satisfies all three clauses of `RenderStep.IsImaginaryUnit`, in a NONCOMMUTATIVE
algebra. -/
theorem isImaginaryUnit_imagUnit : RenderStep.IsImaginaryUnit imagUnit where
  star_eq := by
    rw [imagUnit, star_smul, star_one, Complex.star_def, Complex.conj_I, neg_smul]
  sq_eq := by
    rw [imagUnit, smul_mul_smul_comm, one_mul, Complex.I_mul_I, neg_smul, one_smul]
  central := fun x => by
    rw [imagUnit, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-! ## §4 — THE WHOLE CHAIN AT THE PRINTED OBJECT, AT THE PRINTED SIZE -/

/-- `herm2` is self-adjoint for the matrix `star` (which is `ᴴ`). -/
theorem star_herm2 (x : ℝ) (y : ℂ) : star (TwoByTwo.herm2 x y) = TwoByTwo.herm2 x y :=
  TwoByTwo.herm2_conjTranspose x y

/-- **THE ALGEBRA NORM OF THE PRINTED POTENTIAL IS ITS PRINTED SIZE.**  `‖herm2 x y‖ = |A|`,
constant `1` — the statement the convicted module got as `|A|/√2`. -/
theorem norm_herm2_eq_printed (x : ℝ) (y : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (haa : a ^ 2 = TwoByTwo.printedNormSq x y) :
    ‖TwoByTwo.herm2 x y‖ = a :=
  RenderStep.norm_eq_printed (TwoByTwo.herm2 x y) (star_herm2 x y) a ha
    (TwoByTwo.herm2_sq x y a haa)

/-- **THE RENDERING STEP AT THE PRINTED OBJECT.**

`ha` fixes `a = |A|` through the PRINTED norm `|A|² = tr(A*A) = x² + |y|²`
(`TwoByTwo.herm2_printed_normSq`); `hprint` is **CMP99b (3.35)** at the cube's own `Lj`, with no
`√2` adjustment.  Everything else — the group element, its inverse, its norm, the exponential and
Cayley–Hamilton — is discharged. -/
theorem rendering_step_at_herm2 (x : ℝ) (y : ℂ) (a : ℝ)
    (ha : a ^ 2 = TwoByTwo.printedNormSq x y) (haa : 0 ≤ a)
    (η c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 0 < Lj)
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    ‖RenderStep.adOp
        (NormedSpace.exp (η • (imagUnit * TwoByTwo.herm2 x y)))
        (NormedSpace.exp (-(η • (imagUnit * TwoByTwo.herm2 x y)))) - 1‖
      ≤ 2 * RenderStep.linkEps c M α₀ Lj :=
  RenderStep.rendering_step_from_source imagUnit (TwoByTwo.herm2 x y)
    isImaginaryUnit_imagUnit (star_herm2 x y) η a c M α₀ Lj hη hηne haa hLj
    (TwoByTwo.herm2_sq x y a ha) hprint

/-- **THE GROUP-LEVEL STEP AT THE PRINTED OBJECT**, constant `1`. -/
theorem rendering_step_group_at_herm2 (x : ℝ) (y : ℂ) (a : ℝ)
    (ha : a ^ 2 = TwoByTwo.printedNormSq x y) (haa : 0 ≤ a)
    (η c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 0 < Lj)
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    ‖NormedSpace.exp (η • (imagUnit * TwoByTwo.herm2 x y)) - 1‖
      ≤ RenderStep.linkEps c M α₀ Lj :=
  RenderStep.rendering_step_group_from_source imagUnit (TwoByTwo.herm2 x y)
    isImaginaryUnit_imagUnit (star_herm2 x y) η a c M α₀ Lj hη hηne haa hLj
    (TwoByTwo.herm2_sq x y a ha) hprint

/-- **CONTROL, AND THE CORRECTED NUMBER.**  At `x = 1, y = 0` the printed size is `a = 1` — the
convicted module recorded `a = √2` at the same matrix.  `1 ≠ √2`, so the two conventions are
separated here by a theorem, not by a remark. -/
theorem herm2_printed_size_at_pauli3 :
    (1 : ℝ) ^ 2 = TwoByTwo.printedNormSq 1 0 := by
  rw [TwoByTwo.printedNormSq]
  simp

/-- **CONTROL.**  The convicted size at the same matrix, `√2`, is NOT the printed size. -/
theorem convicted_size_ne_printed_size_at_pauli3 :
    Real.sqrt 2 ≠ (1 : ℝ) := by
  intro h
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    have hs : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using hs
  rw [h] at hlt
  exact lt_irrefl 1 hlt

/-- **CONTROL.**  The operator norm of `σ₃` is `1`, matching its printed size — a two-path check of
`norm_herm2_eq_printed` at a point where the value is independently known. -/
theorem norm_pauli3_eq_one : ‖TwoByTwo.herm2 1 0‖ = (1 : ℝ) :=
  norm_herm2_eq_printed 1 0 1 (by norm_num) herm2_printed_size_at_pauli3

/-- **CONTROL.**  Likewise `‖σ₁‖ = 1`. -/
theorem norm_pauli1_eq_one : ‖TwoByTwo.herm2 0 1‖ = (1 : ℝ) := by
  refine norm_herm2_eq_printed 0 1 1 (by norm_num) ?_
  rw [TwoByTwo.printedNormSq]
  simp

end Carrier
