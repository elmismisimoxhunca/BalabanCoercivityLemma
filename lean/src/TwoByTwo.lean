/-
# `TwoByTwo` — the printed potential `A`, and its square, UNDER THE SOURCE'S OWN NORMALIZED TRACE.

LANE `compute/rendering_step_v2/`.  Write scope: that directory only.  Never `lake build`.

**THIS MODULE SUPERSEDES `compute/rendering_step/stage/TwoByTwo.lean`, WHICH IS CONVICTED.**
That module read CMP99b's `|X|² = tr X*X` with the UNNORMALIZED trace `Tr` (Mathlib's
`Matrix.trace`), obtaining `A·A = (|A|²/2)·1`.  The source fixes the opposite convention on the
page where it defines the inner product.

## THE TWO CONVENTIONS, STATED EXPLICITLY SO NO READER REPEATS THE ERROR

Both sentences are from the SAME paper (Bałaban, *Comm. Math. Phys.* **99** (1985) 389–434),
read at 400 dpi from
`compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf`
(sha256 `39f8033b35838c7bdd14f97c7fb1edb0b35d4190b8b88f31d19d12a72d542861`, offset 388, so
printed 390 = pdf 2 and printed 392 = pdf 4; crops `probe/img/c_p390_a.png`, `probe/img/c_p392_top.png`).

> **printed p.390, VERBATIM:** "We will use the notations, the methods and the results of [1–5].
> Let us remark only that in this paper a norm `|X|` of a `N × N` matrix means the Hilbert–Schmidt
> norm: `|X|² = tr X*X`."

> **printed p.392, first line, VERBATIM:** "by `X · Y = tr XY`.  **Let us recall that the trace is
> normalized, i.e., `tr 1 = 1`.**  For example,"

Hence, writing `Tr` for the ordinary trace (Mathlib's `Matrix.trace`) and `tr` for the source's:

| symbol | meaning | this file |
|---|---|---|
| `Tr X` | ordinary trace, `Tr 1 = N` | `Matrix.trace` |
| `tr X` | **the source's** normalized trace, `tr 1 = 1`; for `N = 2`, `tr = ½ Tr` | `ntr` |
| `\|X\|` | **the printed norm**, `\|X\|² = tr X*X` | `printedNormSq` |

`ntr` is pinned by `ntr_one` (`ntr 1 = 1`) — the source's own sentence as an equation — and
`trace_one_ne_one` proves the UNNORMALIZED trace fails that sentence.  **Uniform-rescale test:
multiply `ntr` by any `c ≠ 1` and `ntr_one` is false.**

## Consequences, all with constant ONE

For the traceless Hermitian `A = herm2 x y`:

* `Tr(A*A) = 2(x² + |y|²)`  (`herm2_unnormalized_trace`)
* `|A|² = tr(A*A) = x² + |y|²`  (`herm2_printed_normSq`)
* **Cayley–Hamilton: `A·A = |A|²·1`** — constant `1`, not `1/2`  (`herm2_sq`)

`A` is CMP99b's gauge potential in the Hermitian presentation (`U′ = exp(iηA)`, recorded in the
tree at `formal/AdalyFormal/DELTA_PRIME_BUILD.md:57`).

This module is deliberately NORM-FREE: pure matrix algebra, imports nothing from `RenderStep`.

Nothing here is graded by this lane (BUILD DISCIPLINE 8); it reports facts.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

namespace TwoByTwo

open Matrix

/-! ## §0 — THE SOURCE'S TRACE, AND WHAT PINS IT -/

/-- **THE SOURCE'S TRACE** on `2×2` matrices: `tr = ½ Tr`.  CMP99b p.392: *"Let us recall that the
trace is normalized, i.e., `tr 1 = 1`."*  The factor `½` is `N⁻¹` at `N = 2`; it is NOT elective —
`ntr_one` fails for any other factor. -/
noncomputable def ntr (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (1 / 2) * A.trace

/-- **THE NORMALIZATION, AS THE SOURCE STATES IT.**  `tr 1 = 1`.  This is the assertion that fixes
the `½`: rescale `ntr` by any `c ≠ 1` and this equation is false. -/
theorem ntr_one : ntr (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  simp [ntr, Matrix.trace_one]

/-- **THE CONVICTED READING FAILS THE SOURCE'S OWN SENTENCE.**  Mathlib's `Matrix.trace` gives
`Tr 1 = 2 ≠ 1`, so it is not the `tr` of CMP99b. -/
theorem trace_one_ne_one : (1 : Matrix (Fin 2) (Fin 2) ℂ).trace ≠ 1 := by
  rw [Matrix.trace_one]
  norm_num

/-- The two traces differ by exactly the factor `2` — the whole content of the correction. -/
theorem trace_eq_two_mul_ntr (A : Matrix (Fin 2) (Fin 2) ℂ) : A.trace = 2 * ntr A := by
  rw [ntr]; ring

/-! ## §1 — THE PRINTED POTENTIAL -/

/-- The printed potential at one link: a traceless Hermitian `2×2` complex matrix, in the general
parametrisation `x : ℝ` (the diagonal) and `y : ℂ` (the off-diagonal). -/
def herm2 (x : ℝ) (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), y; (starRingEnd ℂ) y, -(x : ℂ)]

/-- `herm2` is Hermitian — the `star A = A` hypothesis of `RenderStep`. -/
theorem herm2_conjTranspose (x : ℝ) (y : ℂ) : (herm2 x y)ᴴ = herm2 x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [herm2, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- `herm2` is traceless — under BOTH conventions, since `tr` and `Tr` differ by a nonzero factor. -/
theorem herm2_trace (x : ℝ) (y : ℂ) : (herm2 x y).trace = 0 := by
  simp [herm2, Matrix.trace_fin_two]

/-- `herm2` is traceless for the source's normalized trace too. -/
theorem herm2_ntr (x : ℝ) (y : ℂ) : ntr (herm2 x y) = 0 := by
  rw [ntr, herm2_trace]; ring

/-! ## §2 — THE PRINTED NORM `|A|² = tr A*A` -/

/-- The UNNORMALIZED trace of `A*A`: `Tr(A*A) = 2(x² + |y|²)`.  Retained ONLY as the contrast that
identifies the convicted reading; it is NOT the printed `|A|²`. -/
theorem herm2_unnormalized_trace (x : ℝ) (y : ℂ) :
    ((herm2 x y)ᴴ * herm2 x y).trace = ((2 * (x ^ 2 + Complex.normSq y) : ℝ) : ℂ) := by
  rw [herm2_conjTranspose]
  have hstep : (herm2 x y * herm2 x y).trace = 2 * ((x : ℂ) ^ 2 + y * (starRingEnd ℂ) y) := by
    simp [herm2, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hstep, Complex.mul_conj]
  push_cast
  ring

/-- **THE PRINTED SIZE.**  `|A|² = tr(A*A) = x² + |y|²`, with the source's normalized trace. -/
noncomputable def printedNormSq (x : ℝ) (y : ℂ) : ℝ := x ^ 2 + Complex.normSq y

/-- **THE PRINTED NORM, PROVED.**  `tr(A*A) = |A|²` with `tr` the source's normalized trace. -/
theorem herm2_printed_normSq (x : ℝ) (y : ℂ) :
    ntr ((herm2 x y)ᴴ * herm2 x y) = ((printedNormSq x y : ℝ) : ℂ) := by
  rw [ntr, herm2_unnormalized_trace, printedNormSq]
  push_cast
  ring

/-- **THE CORRECTION, AS A NUMBER.**  At `x = 1, y = 0` (the matrix `diag(1,−1)`) the printed size
is `|A|² = 1`, while the convicted reading gives `2`.  They are NOT equal — so the two conventions
are separated by a theorem, not by a remark. -/
theorem printed_ne_unnormalized_at_pauli3 :
    ntr ((herm2 1 0)ᴴ * herm2 1 0) ≠ ((herm2 1 0)ᴴ * herm2 1 0).trace := by
  rw [herm2_printed_normSq, herm2_unnormalized_trace, printedNormSq]
  norm_num

/-! ## §3 — CAYLEY–HAMILTON, WITH THE PRINTED CONSTANT `1` -/

/-- **CAYLEY–HAMILTON UNDER THE PRINTED CONVENTION.**  `A·A = |A|²·1` for a traceless Hermitian
`2×2` `A` with printed size `a = |A|`, i.e. `a² = x² + |y|²`.

The convicted module asserted `A·A = (a²/2)·1`; that is this identity with `a` replaced by the
unnormalized size `√2·a`. -/
theorem herm2_sq (x : ℝ) (y : ℂ) (a : ℝ) (ha : a ^ 2 = printedNormSq x y) :
    herm2 x y * herm2 x y = (a ^ 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hval : ((a ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 + y * (starRingEnd ℂ) y := by
    rw [Complex.mul_conj, ha, printedNormSq]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [herm2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
      Complex.real_smul, hval] <;> ring

/-- **CONTROL.**  The identity is not vacuous: at `x = 1`, `y = 0` the matrix is `diag(1,−1)`, the
printed size is `|A|² = 1`, and the square is the identity — consistent with `A·A = |A|²·1` at
`|A| = 1`.  (Under the convicted reading the printed size would be `2` and the same equation would
force `A·A = 2·1`, which is FALSE; that is `herm2_sq_convicted_constant_false` below.) -/
theorem herm2_sq_pauli3 :
    herm2 1 0 * herm2 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [herm2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **THE CONVICTED CONSTANT IS FALSE AT THE PRINTED SIZE.**  With `a = |A|` the PRINTED size, the
old identity `A·A = (a²/2)·1` fails at `x = 1, y = 0` (`a² = 1`): it would give `A·A = ½·1`, but
`A·A = 1`.  So the two readings are not interchangeable — one of them is wrong, and the page says
which. -/
theorem herm2_sq_convicted_constant_false :
    herm2 1 0 * herm2 1 0 ≠ (((1 : ℝ) ^ 2 / 2 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  rw [herm2_sq_pauli3] at h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [Matrix.one_apply, Matrix.smul_apply, Complex.real_smul] at h00

/-- **CONTROL.**  `herm2` is not the zero matrix for generic data — the class is non-trivial. -/
theorem herm2_ne_zero_of_x_ne_zero (x : ℝ) (y : ℂ) (hx : x ≠ 0) :
    herm2 x y ≠ 0 := by
  intro h
  have h00 : herm2 x y 0 0 = 0 := by rw [h]; rfl
  simp [herm2] at h00
  exact hx h00

/-- **CONTROL.**  `herm2` is NOT central: it does not commute with every matrix, so the adjoint
step of `RenderStep` §2 is non-trivial on this carrier. -/
theorem herm2_not_central :
    herm2 1 0 * herm2 0 1 ≠ herm2 0 1 * herm2 1 0 := by
  intro h
  have h01 : (herm2 1 0 * herm2 0 1) 0 1 = (herm2 0 1 * herm2 1 0) 0 1 := by rw [h]
  simp [herm2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- **CONTROL.**  `σ₁ = herm2 0 1` squares to `1` as well — used by the cross-cube witness as a
unit-norm test vector for the adjoint operator. -/
theorem herm2_sq_pauli1 :
    herm2 0 1 * herm2 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [herm2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **CONTROL.**  `σ₃ σ₁ σ₃ = −σ₁` — the explicit non-triviality of the adjoint action used by the
cross-cube witness. -/
theorem pauli3_conj_pauli1 :
    herm2 1 0 * herm2 0 1 * herm2 1 0 = -(herm2 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [herm2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end TwoByTwo
