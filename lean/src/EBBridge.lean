/-
`compute/gauge_patching/stage/EBBridge.lean`

**THE ONE COMPOSITION STEP BETWEEN THE PRINTED SIZE AND THIS CHAIN'S HYPOTHESIS, CLOSED.**

`JLocality`/`PartialCover` take their smallness hypothesis in the ENTRYWISE form `EB δ (U(b) − 1)`,
which is what `SourceWiredJ`'s `495·δ` chain consumes.  CMP99b states its own smallness in a NORM:
printed p.390 (`corpus/pages/CMP99b_p390.md`, and re-read at the image by
`compute/rendering_step_v2/` §1(a)):

> "in this paper a norm `|X|` of a `N × N` matrix means the Hilbert–Schmidt norm: `|X|² = tr X*X`."

together with printed p.392, first line (same lane, §1(b)):

> "Let us recall that the trace is normalized, i.e., `tr 1 = 1`."

At `N = 2` that is `|X|² = ½ Σ_{ij} |X_ij|²`.  This file proves the conversion, with the constant
COUNTED and shown SHARP:

    |X| ≤ a   ⟹   EB (√2 · a) X ,      and √2 cannot be lowered.

so a lane holding the printed norm bound (that is `compute/rendering_step_v2/`'s output shape) can
enter `JLocality`'s hypothesis with one multiplication and no unexamined step.

**Disclosed, and NOT claimed:** `compute/rendering_step_v2/stage/TwoByTwo.lean` has its own
`printedNormSq` on its own abstract carrier.  This file does not pin or import it; the definition
here is written independently from the two printed sentences above, at the concrete
`Matrix (Fin 2) (Fin 2) ℂ` carrier this chain uses.  Agreement of the two is not asserted.
Also NOT claimed here: the exponential step `U = exp(iηA) ⟹ |U − 1| ≤ η|A|`, which is
`rendering_step_v2`'s and is not reproved (LAW-19).
-/
import JLocality

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.Balaban.GaugePatching.EBBridge

open Matrix
open AdalyFormal.Balaban.SourceWiredJ (EB)

/-- **`|X|²` at `N = 2`**, from the two printed sentences: Hilbert–Schmidt with the NORMALIZED
trace, i.e. `|X|² = ½ Σ_{ij} |X_ij|²`. -/
noncomputable def printedNormSq (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1 / 2) * ∑ i : Fin 2, ∑ j : Fin 2, ‖X i j‖ ^ 2

/-- **The source's own sentence, as an equation**: `|1| = 1`, i.e. `tr 1 = 1`.  A convention that
dropped the `½` would give `2` here, so this pins the normalization (uniform-rescale test). -/
theorem printedNormSq_one : printedNormSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  unfold printedNormSq
  simp [Matrix.one_apply, Fin.sum_univ_two]
  norm_num

theorem printedNormSq_nonneg (X : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ printedNormSq X := by
  unfold printedNormSq
  positivity

/-- Each entry's square is bounded by the full sum. -/
theorem entry_sq_le_sum (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ‖X i j‖ ^ 2 ≤ ∑ p : Fin 2, ∑ q : Fin 2, ‖X p q‖ ^ 2 := by
  have hj : ‖X i j‖ ^ 2 ≤ ∑ q : Fin 2, ‖X i q‖ ^ 2 :=
    Finset.single_le_sum (f := fun q => ‖X i q‖ ^ 2) (fun q _ => by positivity)
      (Finset.mem_univ j)
  have hi : (∑ q : Fin 2, ‖X i q‖ ^ 2) ≤ ∑ p : Fin 2, ∑ q : Fin 2, ‖X p q‖ ^ 2 :=
    Finset.single_le_sum (f := fun p => ∑ q : Fin 2, ‖X p q‖ ^ 2)
      (fun p _ => by positivity) (Finset.mem_univ i)
  linarith

/-- **THE BRIDGE.**  The printed norm bound gives the entrywise bound this chain consumes.
The constant is `√2` and it is COUNTED: `Σ_{ij}|X_ij|² = 2·|X|²` by the `½` in the normalized
trace, and each single entry is at most the whole sum. -/
theorem EB_of_printedNormSq_le (X : Matrix (Fin 2) (Fin 2) ℂ) {a : ℝ} (ha : 0 ≤ a)
    (h : printedNormSq X ≤ a ^ 2) : EB (Real.sqrt 2 * a) X := by
  intro i j
  have hsum : (∑ p : Fin 2, ∑ q : Fin 2, ‖X p q‖ ^ 2) = 2 * printedNormSq X := by
    unfold printedNormSq; ring
  have h1 : ‖X i j‖ ^ 2 ≤ 2 * a ^ 2 := by
    have := entry_sq_le_sum X i j
    rw [hsum] at this
    nlinarith [this, h]
  have h2 : (Real.sqrt 2 * a) ^ 2 = 2 * a ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hnn : 0 ≤ Real.sqrt 2 * a := by positivity
  nlinarith [h1, h2, norm_nonneg (X i j), hnn]

/-- **THE CONSTANT IS SHARP.**  At `X = e₀₀` the printed size is `√(1/2)` and the largest entry is
`1 = √2 · √(1/2)`, so no constant below `√2` works. -/
noncomputable def e00 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![1, 0], ![0, 0]]

theorem printedNormSq_e00 : printedNormSq e00 = 1 / 2 := by
  unfold printedNormSq e00
  simp [Matrix.of_apply, Fin.sum_univ_two]

theorem e00_entry : ‖e00 0 0‖ = 1 := by
  simp [e00, Matrix.of_apply]

theorem EB_constant_sharp {c : ℝ} (hc : c < Real.sqrt 2) :
    ¬ (∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∀ a : ℝ, 0 ≤ a → printedNormSq X ≤ a ^ 2 → EB (c * a) X) := by
  intro hall
  have hsq : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have h := hall e00 (Real.sqrt (1 / 2 : ℝ)) hnn (by rw [printedNormSq_e00, hsq])
  have h00 := h 0 0
  rw [e00_entry] at h00
  -- `c * √(1/2) < √2 * √(1/2) = 1`
  have hpos : (0 : ℝ) < Real.sqrt (1 / 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hprod : Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  nlinarith [h00, hpos, hprod, mul_lt_mul_of_pos_right hc hpos]

#print axioms printedNormSq_one
#print axioms printedNormSq_nonneg
#print axioms entry_sq_le_sum
#print axioms EB_of_printedNormSq_le
#print axioms printedNormSq_e00
#print axioms e00_entry
#print axioms EB_constant_sharp

end AdalyFormal.Balaban.GaugePatching.EBBridge
