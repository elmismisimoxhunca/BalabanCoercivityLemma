/-
# `PrintedToAlpha` — CMP99b (3.35) converted into the coercivity chain's own `α₁`.

LANE `compute/threshold_vs_printed/`.  Write scope: that directory only.  Never `lake build`.

## THE QUESTION

`compute/stokes_hraw/` closed the drift bound for EVERY background, with the constant exhibited:
positivity of the coercivity floor is EXACTLY `5184·(α₁·‖H₁‖)² < γ_P·ℓ`, where
`α₁ = RegularUPerturbation.frobSupBond U = sup_b ‖U(b) − 1‖_Frobenius`.

CMP99b p.396 (3.35) is a smallness condition too.  **Does the printed one imply ours?**

## THE PRINTED SOURCE, IMAGE-VERIFIED (LAW-11)

`corpus/renders/CMP99b_p396-08.png`, sha256
`d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec`; corpus page
`corpus/pages/CMP99b_p396.md`, `verification_status: adjudicated`.  VERBATIM:

> for an arbitrary cube □ of the described above class, and for a configuration `U` there exists a
> gauge transformation `u` on □ such that `U^u = e^{iηA}`, and if the index of □ is `j`, then
>
> `|A| < O(1) M α₀ (L^j η)^{-1}`, `|∇^η A| < O(1) M α₀ (L^j η)^{-2}` on □,
> where `O(1)M` is a size of □ in `T_{L^{-j}}`;   (3.35)

> The number `α₀` characterizes this class of configurations.  We will need `α₀` so small that
> `O(1)Mα₀` is still a sufficiently small number.

> Here `O(1)` will mean a number `≥ 10`.

The exponent glyph was re-checked at 5× magnification on the render: the character after `i` carries
a DESCENDER and is the same glyph as the `η` of `(L^jη)^{-1}` and of `∇^η`.  It is `e^{iηA}`, not
`e^{inA}`.  That mesh `η` is what cancels against `(L^jη)^{-1}`, so the glyph is load-bearing.
`|A|` is a POINTWISE magnitude ("on □"), not an aggregate over the cube.

The printed norm is fixed by two further sentences of the SAME paper, both already in the tree's
corpus and both re-read here:
* p.390: *"a norm `|X|` of a `N × N` matrix means the Hilbert–Schmidt norm: `|X|² = tr X*X`"*;
* p.392: *"Let us recall that the trace is normalized, i.e., `tr 1 = 1`."*

so at `N = 2`, `|X|² = ½·Tr(X*X) = ½·frobSq X`.

## WHAT THIS MODULE PROVES

§1  the norm bridge, as an EQUALITY: `frobNorm X = √2 · |X|`.  The `√2` is exact and attained.
§2  `|X| ≤ ‖X‖_op` at `2×2` (equivalently `frobNorm X ≤ √2·‖X‖_op`), and its sharpness.
§3  the composition with `rendering_step_v2`'s exponential step: (3.35) ⟹ `‖U^u(b) − 1‖_F ≤ √2·s`
    with `s := O(1)Mα₀` the source's OWN smallness parameter — the mesh `η` and the level `L^j`
    both cancel.
§4  the `frobSupBond` form, and the `frobSupBond`-is-gauge-DEPENDENT witness.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/
import Mathlib
import Carrier
import AdalyFormal.Balaban.RegularUPerturbation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

namespace ThresholdVsPrinted

open scoped Matrix.Norms.L2Operator
open AdalyFormal.Balaban

/-- The `2×2` complex matrices with the `l²` operator norm — the algebra `SU(2)` acts on.
Same carrier as `Carrier.M2`, named here for readability. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-! ## §1 — THE PRINTED NORM AND THE EXACT `√2` BRIDGE -/

/-- **CMP99b's printed squared norm at `N = 2`.**  `|X|² = tr(X*X)` with the NORMALIZED trace
(`tr 1 = 1`), i.e. `½·Tr(X*X) = ½·frobSq X`.  Defined from `RMapLipschitz.frobSq` so that the object
being converted is literally the one `frobSupBond` is built from. -/
noncomputable def printedNormSq (X : M2) : ℝ := (1 / 2) * RMapLipschitz.frobSq X

/-- **THE PIN.**  `|1| = 1` — the source's own sentence *"the trace is normalized, i.e. `tr 1 = 1`"*
as an equation.  Any other constant in `printedNormSq` breaks it: `frobSq 1 = 2`. -/
theorem printedNormSq_one : printedNormSq (1 : M2) = 1 := by
  unfold printedNormSq RMapLipschitz.frobSq
  norm_num [Matrix.one_apply]

/-- `frobSq 1 = 2` — recorded separately so the `½` of `printedNormSq` is visibly the thing that
turns `2` into `1`, rather than a convention asserted in prose. -/
theorem frobSq_one : RMapLipschitz.frobSq (1 : M2) = 2 := by
  unfold RMapLipschitz.frobSq
  norm_num [Matrix.one_apply]

theorem printedNormSq_nonneg (X : M2) : 0 ≤ printedNormSq X := by
  unfold printedNormSq
  have := RMapLipschitz.frobSq_nonneg X
  linarith

/-- **`frobSq X = 2·|X|²`** — the bridge at the level of squares. -/
theorem frobSq_eq_two_mul_printedNormSq (X : M2) :
    RMapLipschitz.frobSq X = 2 * printedNormSq X := by
  unfold printedNormSq; ring

/-- **THE NORM BRIDGE, AS AN EQUALITY: `‖X‖_F = √2 · |X|`.**  Nothing is lost in this conversion —
it is not an estimate.  This is the `√2` that the entrywise bridge of `compute/gauge_patching/`
proved sharp; in the Frobenius form the constant is exact by construction. -/
theorem frobNorm_eq_sqrt_two_mul_printed (X : M2) :
    RMapLipschitz.frobNorm X = Real.sqrt 2 * Real.sqrt (printedNormSq X) := by
  unfold RMapLipschitz.frobNorm
  rw [frobSq_eq_two_mul_printedNormSq X,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (printedNormSq X)]

/-- The `√2` of the bridge is ATTAINED at `X = 1`: `‖1‖_F = √2` while `|1| = 1`. -/
theorem frobNorm_one : RMapLipschitz.frobNorm (1 : M2) = Real.sqrt 2 := by
  unfold RMapLipschitz.frobNorm; rw [frobSq_one]

/-! ## §2 — THE PRINTED NORM IS DOMINATED BY THE OPERATOR NORM, AT `2×2`

`|X|² = ½(σ₁² + σ₂²) ≤ σ_max² = ‖X‖_op²`.  Proved here without singular values, by testing the
operator on the two standard basis vectors: the `j`-th column's squared `ℓ²` norm is at most
`‖X‖_op²`, and `frobSq` is the sum of the two column norms. -/

/-- The squared `ℓ²` norm of the `j`-th column of `X` is at most `‖X‖_op²`. -/
theorem col_normSq_le_opNorm_sq (X : M2) (j : Fin 2) :
    ∑ i : Fin 2, Complex.normSq (X i j) ≤ ‖X‖ ^ 2 := by
  classical
  set v : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single j (1 : ℂ) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, EuclideanSpace.norm_single]; simp
  have hmul := Matrix.l2_opNorm_mulVec X v
  rw [hvnorm, mul_one] at hmul
  -- the transported vector is exactly the `j`-th column
  have hvofLp : v.ofLp = Pi.single j (1 : ℂ) := by
    rw [hv]; simp
  have hofLp : ((EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec v.ofLp)).ofLp
      = X.mulVec v.ofLp := rfl
  have hcol : ∀ i : Fin 2,
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec v.ofLp)).ofLp i = X i j := by
    intro i
    rw [hofLp, hvofLp, Matrix.mulVec_single]
    simp
  have hnormsq : ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec v.ofLp)‖ ^ 2
      = ∑ i : Fin 2, Complex.normSq (X i j) := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcol i, Complex.normSq_eq_norm_sq]
  calc ∑ i : Fin 2, Complex.normSq (X i j)
      = ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec v.ofLp)‖ ^ 2 := hnormsq.symm
    _ ≤ ‖X‖ ^ 2 := by
        have h0 : (0:ℝ) ≤ ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec v.ofLp)‖ := norm_nonneg _
        nlinarith [hmul, h0, norm_nonneg X]

/-- **`frobSq X ≤ 2·‖X‖_op²`** — the two columns, summed. -/
theorem frobSq_le_two_mul_opNorm_sq (X : M2) :
    RMapLipschitz.frobSq X ≤ 2 * ‖X‖ ^ 2 := by
  have h0 := col_normSq_le_opNorm_sq X 0
  have h1 := col_normSq_le_opNorm_sq X 1
  simp only [Fin.sum_univ_two] at h0 h1
  unfold RMapLipschitz.frobSq
  linarith

/-- **`|X| ≤ ‖X‖_op`** at `2×2` — the printed norm is an AVERAGE of squared singular values, so it
never exceeds the operator norm.  This is the direction the conversion needs. -/
theorem printedNormSq_le_opNorm_sq (X : M2) : printedNormSq X ≤ ‖X‖ ^ 2 := by
  have := frobSq_le_two_mul_opNorm_sq X
  unfold printedNormSq
  linarith

/-- **`‖X‖_F ≤ √2 · ‖X‖_op`** — §1 and §2 composed.  This is the ONLY inequality in the whole
conversion; §1 is an equality and §3's exponential step is an equality-then-(3.35). -/
theorem frobNorm_le_sqrt_two_mul_opNorm (X : M2) :
    RMapLipschitz.frobNorm X ≤ Real.sqrt 2 * ‖X‖ := by
  rw [frobNorm_eq_sqrt_two_mul_printed X]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
  calc Real.sqrt (printedNormSq X) ≤ Real.sqrt (‖X‖ ^ 2) :=
        Real.sqrt_le_sqrt (printedNormSq_le_opNorm_sq X)
    _ = ‖X‖ := Real.sqrt_sq (norm_nonneg X)

/-- **THE `√2` OF §2 IS ATTAINED, SO IT CANNOT BE LOWERED.**  At `X = 1`: `‖1‖_F = √2` and
`‖1‖_op = 1`.  Hence no constant `< √2` works in `frobNorm_le_sqrt_two_mul_opNorm`. -/
theorem sqrt_two_sharp_at_one :
    RMapLipschitz.frobNorm (1 : M2) = Real.sqrt 2 * ‖(1 : M2)‖ := by
  rw [frobNorm_one, norm_one, mul_one]

/-- The sharpness, in refutation form: any `K` valid for ALL `X` obeys `√2 ≤ K`. -/
theorem sqrt_two_is_least (K : ℝ) (hK : ∀ X : M2, RMapLipschitz.frobNorm X ≤ K * ‖X‖) :
    Real.sqrt 2 ≤ K := by
  have h := hK 1
  rw [frobNorm_one, norm_one, mul_one] at h
  exact h

/-! ## §3 — (3.35) ⟹ THE FROBENIUS LINK BOUND, WITH THE MESH AND THE LEVEL CANCELLED

`RenderStep.rendering_step_group_from_source` (pinned from `compute/rendering_step_v2/`, kernel
checked there and recompiled here) delivers, in the operator norm,

    ‖exp(η•(J·A)) − 1‖ ≤ linkEps c M α₀ Lj = c·M·α₀ / Lj

from the printed hypotheses `star A = A`, `A·A = a²•1` (Cayley–Hamilton at the NORMALIZED trace) and
`a ≤ printedABound c M α₀ Lj η = c·M·α₀/(Lj·η)`, which IS (3.35).  §1–§2 convert its conclusion. -/

/-- **THE CONVERSION, AT THE PRINTED OBJECT.**  Hypotheses are exactly the printed ones; the
conclusion is in the norm `frobSupBond` is built from.  Constant: `√2`, and nothing else. -/
theorem printed_to_frobNorm (J A : M2) (hJ : RenderStep.IsImaginaryUnit J) (hA : star A = A)
    (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 0 < Lj)
    (hsq : A * A = (a ^ 2) • (1 : M2))
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    RMapLipschitz.frobNorm (NormedSpace.exp (η • (J * A)) - 1)
      ≤ Real.sqrt 2 * RenderStep.linkEps c M α₀ Lj := by
  refine le_trans (frobNorm_le_sqrt_two_mul_opNorm _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
  exact RenderStep.rendering_step_group_from_source J A hJ hA η a c M α₀ Lj hη hηne ha hLj hsq hprint

/-- **THE LEVEL CANCELS.**  `linkEps c M α₀ Lj = c·M·α₀/L^j ≤ c·M·α₀` whenever `1 ≤ L^j`, which
holds for every `L ≥ 1` and `j ≥ 0`.  `c·M·α₀` is the source's own `O(1)Mα₀`. -/
theorem linkEps_le_smallness (c M α₀ Lj : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hLj : 1 ≤ Lj) : RenderStep.linkEps c M α₀ Lj ≤ c * M * α₀ := by
  unfold RenderStep.linkEps
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hLj)]
  nlinarith [mul_nonneg (mul_nonneg hc hM) hα]

/-- **THE COMPOSED CONVERSION.**  (3.35) at any level `j ≥ 0` of any `L ≥ 1` gives, at every link
the cube's gauge covers,

    ‖U^u(b) − 1‖_Frobenius  ≤  √2 · (O(1)·M·α₀).

`η` has cancelled against `(L^jη)^{-1}`; `L^{-j} ≤ 1`; and `O(1)Mα₀` is EXACTLY the quantity
p.396 says must be "a sufficiently small number".  **The only surviving constant is `√2`.** -/
theorem printed_to_smallness (J A : M2) (hJ : RenderStep.IsImaginaryUnit J) (hA : star A = A)
    (η a c M α₀ Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (ha : 0 ≤ a) (hLj : 1 ≤ Lj)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hα : 0 ≤ α₀)
    (hsq : A * A = (a ^ 2) • (1 : M2))
    (hprint : a ≤ RenderStep.printedABound c M α₀ Lj η) :
    RMapLipschitz.frobNorm (NormedSpace.exp (η • (J * A)) - 1)
      ≤ Real.sqrt 2 * (c * M * α₀) := by
  refine le_trans
    (printed_to_frobNorm J A hJ hA η a c M α₀ Lj hη hηne ha
      (lt_of_lt_of_le zero_lt_one hLj) hsq hprint) ?_
  exact mul_le_mul_of_nonneg_left (linkEps_le_smallness c M α₀ Lj hc hM hα hLj)
    (Real.sqrt_nonneg 2)

/-! ## §4 — THE `frobSupBond` FORM, AND WHAT IT IS A SUP OF

`RegularUPerturbation.frobSupBond U = sup_b ‖U(b) − 1‖_F` is a `Finset.sup'` over ALL bonds, so a
bound on it needs the per-link bound at EVERY bond.  That is the point at which the printed
per-cube `∃u` and this global object part company; §4b makes that concrete. -/

/-- **THE `sup` FORM.**  If every link of `U` obeys the converted printed bound, so does the sup.
This is the hypothesis `stokes_hraw`'s threshold consumes, with `α₁ = frobSupBond U`. -/
theorem frobSupBond_le_of_links {L : AdalyFormal.Target.ClayStatement.PeriodicLatticeExtent}
    (U : AdalyFormal.Target.ClayStatement.PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (s : ℝ)
    (h : ∀ b, RMapLipschitz.frobNorm ((U b : M2) - 1) ≤ Real.sqrt 2 * s) :
    RegularUPerturbation.frobSupBond U ≤ Real.sqrt 2 * s := by
  unfold RegularUPerturbation.frobSupBond
  exact Finset.sup'_le _ _ (fun b _ => h b)

/-- **`frobSupBond` IS NOT GAUGE INVARIANT — and the witness is the flat configuration itself.**
`frobSupBond (trivialU) = 0`, but a gauge that is not constant along a bond makes the same physical
configuration have a strictly positive `frobSupBond`.  Concretely: at `U = 1` and any group element
`g ≠ 1`, the gauged link `g·1·1⁻¹ = g` has `‖g − 1‖_F > 0`.

Stated as the pure algebra it is, so it applies to whatever gauge convention a consumer uses: the
quantity `‖V − 1‖_F` separates group elements, hence CANNOT be a function of the gauge orbit. -/
theorem frobNorm_sub_one_eq_zero_iff (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    RMapLipschitz.frobNorm ((V : M2) - 1) = 0 ↔ (V : M2) = 1 := by
  constructor
  · intro h
    have h2 : RMapLipschitz.frobSq ((V : M2) - 1) = 0 := by
      have := RMapLipschitz.frobNorm_sq ((V : M2) - 1)
      rw [h] at this; simpa using this.symm
    unfold RMapLipschitz.frobSq at h2
    have e00 := Complex.normSq_nonneg (((V : M2) - 1) 0 0)
    have e01 := Complex.normSq_nonneg (((V : M2) - 1) 0 1)
    have e10 := Complex.normSq_nonneg (((V : M2) - 1) 1 0)
    have e11 := Complex.normSq_nonneg (((V : M2) - 1) 1 1)
    have z00 : ((V : M2) - 1) 0 0 = 0 := by
      rw [← Complex.normSq_eq_zero]; linarith
    have z01 : ((V : M2) - 1) 0 1 = 0 := by
      rw [← Complex.normSq_eq_zero]; linarith
    have z10 : ((V : M2) - 1) 1 0 = 0 := by
      rw [← Complex.normSq_eq_zero]; linarith
    have z11 : ((V : M2) - 1) 1 1 = 0 := by
      rw [← Complex.normSq_eq_zero]; linarith
    funext i j
    fin_cases i <;> fin_cases j <;>
      [ (have := z00); (have := z01); (have := z10); (have := z11) ] <;>
      simpa [sub_eq_zero] using this
  · intro h; rw [h]; simp [RMapLipschitz.frobNorm, RMapLipschitz.frobSq]

/-- **THE GAUGE-DEPENDENCE, MADE NUMERIC.**  `‖−1 − 1‖_F = ‖−2·1‖_F = 2√2`.  So a configuration
that is EXACTLY flat (`frobSupBond = 0`) acquires `frobSupBond = 2√2` — the maximum a `2×2` unitary
difference can have — under the gauge that multiplies one endpoint by `−1`.  Hence a per-cube gauge
statement cannot bound `frobSupBond U` itself; it bounds `frobSupBond` OF THE GAUGED CONFIGURATION. -/
theorem frobNorm_negOne_sub_one : RMapLipschitz.frobNorm ((-1 : M2) - 1) = 2 * Real.sqrt 2 := by
  have hfs : RMapLipschitz.frobSq ((-1 : M2) - 1) = 8 := by
    unfold RMapLipschitz.frobSq
    norm_num [Matrix.one_apply]
  unfold RMapLipschitz.frobNorm
  rw [hfs]
  rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ## §5 — VACUITY GUARDS -/

/-- **S82 GARBAGE SUBSTITUTION on §2.**  The bound `frobSq ≤ 2‖X‖²` is NOT algebraically forced:
at `X = 1` it is the equality `2 = 2`, so the constant `2` is attained and cannot be lowered — and
a strictly smaller constant is refuted by this same point. -/
theorem frobSq_two_attained : RMapLipschitz.frobSq (1 : M2) = 2 * ‖(1 : M2)‖ ^ 2 := by
  rw [frobSq_one, norm_one]; norm_num

/-- **THE CONVERSION HAS CONTENT: both sides are strictly positive somewhere.**  At `X = 1`,
`frobNorm 1 = √2 > 0` and `‖1‖_op = 1 > 0`.  So §2 relates two strictly positive numbers rather
than collapsing to `0 ≤ 0`. -/
theorem conversion_nonvacuous : 0 < RMapLipschitz.frobNorm (1 : M2) ∧ 0 < ‖(1 : M2)‖ := by
  refine ⟨?_, by rw [norm_one]; norm_num⟩
  rw [frobNorm_one]
  exact Real.sqrt_pos.mpr (by norm_num)

/-- **`α₀ = 0` DOES NOT MAKE §3 VACUOUS — it makes it EXACT.**  At `α₀ = 0` the printed bound forces
`a = 0`, `A = 0`, `exp 0 = 1`, and both sides are `0`.  Recorded so that the degenerate point is a
theorem rather than an unexamined corner. -/
theorem smallness_at_zero (c M : ℝ) : Real.sqrt 2 * (c * M * 0) = 0 := by ring

end ThresholdVsPrinted
