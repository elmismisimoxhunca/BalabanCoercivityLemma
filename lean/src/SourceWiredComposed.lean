/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import SourceWiredThreshold
import SourceWiredJ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# THE WIRED STATEMENT: `γ₀` UNIFORM IN `U`, WITH THE SOURCE INSTANTIATED AT `J(U)`

`SourceWiredThreshold.lean` gives the coercivity constant `γ₁ − 2‖H₁‖c₂‖J‖` for the printed
(3.156) form.  `SourceWiredJ.lean` gives `‖J(U)‖ ≤ √(2|Bond L|)·495·δ`, uniformly over the whole
configuration space at `δ = 2` and linearly in the link deviation `δ` otherwise.  This file
composes them, in the exact quantifier order CMP99b p.428 uses: **one constant, then all `U`.**

## The three statements

1. **`wired_coercive_uniform_in_U`** — with the source of EVERY configuration bounded by one `R`,
   the printed `Δ_k(U)` is coercive with the SAME constant `γ₁ − 2‖H₁‖c₂R` at every `U`.  This is
   `∃γ₀ ∀U`, not `∀U ∃γ₀`.
2. **`norm_source_le_of_linkDev`** — the hypothesis of (1) is met by the printed `J(U)`, carried
   into the `A`-space by ANY bounded linear `T`, with `R = ‖T‖√(2|Bond L|)·495·δ`.  No collapse of
   the `A`- and `B`-spaces is needed: `T` is left abstract.
3. **`bondData_wired_posDef`** — an instance with `γ₁` COMPUTED (`= 1/2 − a`), not hypothesized,
   so the chain is exhibited end-to-end at least once.

## What is disclosed

* `LinkDev δ U` (below) is a smallness hypothesis on the configuration: every entry of `U(b) − 1`
  is `≤ δ`.  It is **NOT** CMP99b (3.35)/(3.36).  Those conditions give `U = exp(iηA)` with
  `|A| < O(1)Mα₀(L^jη)⁻¹` **after a gauge transformation chosen per cube** (`corpus/pages/
  CMP99b_p396.md`), so deriving a global `LinkDev` bound from them needs a gauge-patching argument
  that is NOT performed here.  What is proved here is the implication `LinkDev δ ⇒ coercivity`,
  with `δ` explicit; the implication `(3.35)+(3.36)+Mα₀ small ⇒ LinkDev δ` is the named residual.
* Statement (3) uses `deltak_wiring`'s `bondData`, whose `Q := I` is not Bałaban's block average
  (`DeltaKWiring.collapsed_Q_bijective` costs the collapse explicitly).  It is a non-vacuity
  witness, not Bałaban's geometry.
* Nothing here proves `γ₁ > 0` for Bałaban's own covariance.  That is the OTHER half of the printed
  claim — CMP99b p.428's own *"[4], Lemma 2.4, for operators with `U = 1`"* — and it is untouched.
-/

namespace AdalyFormal.Balaban.SourceWired

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (sourceTerm deltaKQuadOp IsSourceOperator printedDeltaKOp
  inner_printedDeltaKOp inner_deltaKQuadOp cdcFormTrue norm_cZero_pos bondData bondQext
  bondDtilde2 bondData_H1 bondData_isSourceOperator)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo norm_JsuTwo_le norm_JsuTwo_le_uniform
  EB_su2_dev_two)

variable {L : PeriodicLatticeExtent}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## §1 — the configuration class -/

/-- **`LinkDev δ U`**: every entry of `U(b) − 1` has modulus at most `δ`, at every bond.  A
smallness hypothesis on the gauge configuration — see the module docstring for exactly what it is
and is not. -/
def LinkDev (δ : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Prop :=
  ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)

/-- **Every configuration satisfies `LinkDev 2`** — the unconditional fact behind
`norm_JsuTwo_le_uniform`. -/
theorem linkDev_two (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    LinkDev 2 U := fun b => EB_su2_dev_two (U b)

/-! ## §2 — the source of the whole class is bounded by ONE number -/

/-- **THE UNIFORM SOURCE BOUND, THROUGH AN ARBITRARY BOUNDED EMBEDDING.**  `T` carries the
fine-lattice source into whatever space `J` lives in; the bound survives with `‖T‖` as the only
extra factor, so no identification of the `A`- and `B`-spaces is needed. -/
theorem norm_source_le_of_linkDev (T : BondFnL2 L →L[ℝ] H) {δ : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hU : LinkDev δ U) :
    ‖T (JsuTwo U)‖ ≤ ‖T‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ)) := by
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  exact mul_le_mul_of_nonneg_left (norm_JsuTwo_le U hU) (norm_nonneg _)

/-- The same at `δ = 2`, valid for EVERY configuration with no hypothesis at all. -/
theorem norm_source_le_uniform (T : BondFnL2 L →L[ℝ] H)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖T (JsuTwo U)‖ ≤ ‖T‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * 990) := by
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  exact mul_le_mul_of_nonneg_left (norm_JsuTwo_le_uniform U) (norm_nonneg _)

/-- **NO CONFIGURATION REACHES A LARGE SOURCE.**  Past the uniform radius, a vector is not the
image of ANY configuration's `J(U)` — the scaling `cdcFormTrue_unbounded_below_in_J` relies on is
unavailable once `J` is the printed, `U`-determined one. -/
theorem source_not_reachable_of_norm_gt (T : BondFnL2 L →L[ℝ] H) (J : H)
    (hJ : ‖T‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * 990) < ‖J‖)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    T (JsuTwo U) ≠ J := by
  intro h
  have := norm_source_le_uniform T U
  rw [h] at this
  linarith

#print axioms norm_source_le_of_linkDev
#print axioms norm_source_le_uniform
#print axioms source_not_reachable_of_norm_gt

/-! ## §3 — `γ₀` UNIFORM IN `U`

The quantifier order of CMP99b p.428's own sentence (*"a lower bound `γ₀ > 0` independent of `k`
and `U`"*): the constant is written down first, from `γ₁`, `‖H₁‖`, `c₂` and ONE source radius `R`,
and then holds at every configuration. -/

/-- **THE WIRED COERCIVITY, UNIFORM IN `U`.**  `Jof`/`Sof` are the configuration's own source and
its operator representative; `R` bounds the source over the WHOLE class at once. -/
theorem wired_coercive_uniform_in_U (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L)
    (Jof : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L → H)
    (Sof : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L →
      (BondFnL2 L →L[ℝ] BondFnL2 L))
    (hS : ∀ U, IsSourceOperator D Qext (Jof U) (Sof U))
    (γ₁ c₂ R : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hR : ∀ U, ‖Jof U‖ ≤ R)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (B : BondFnL2 L) :
    (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * R) * ‖B‖ ^ 2
      ≤ (inner ℝ B (printedDeltaKOp D bc (Sof U) B) : ℝ) := by
  have hmain := printedDeltaK_coercive_of_source_small D bc Qext (Jof U) (Sof U) (hS U) γ₁ c₂ hc₂
    hfloor hD2 B
  have hcoef : 0 ≤ 2 * ‖solutionOperator D‖ * c₂ := by positivity
  have hstep : (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * R)
      ≤ (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖Jof U‖) := by
    have := mul_le_mul_of_nonneg_left (hR U) hcoef
    linarith
  have hsq : (0 : ℝ) ≤ ‖B‖ ^ 2 := sq_nonneg _
  nlinarith [hmain, hstep, hsq]

#print axioms wired_coercive_uniform_in_U

/-- **THE WIRED POSITIVE DEFINITENESS, UNIFORM IN `U`** — the printed claim's own conclusion once
the class radius is below the threshold. -/
theorem wired_posDef_uniform_in_U (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L)
    (Jof : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L → H)
    (Sof : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L →
      (BondFnL2 L →L[ℝ] BondFnL2 L))
    (hS : ∀ U, IsSourceOperator D Qext (Jof U) (Sof U))
    (γ₁ c₂ R : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hR : ∀ U, ‖Jof U‖ ≤ R)
    (hthr : 2 * ‖solutionOperator D‖ * c₂ * R < γ₁)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (B : BondFnL2 L)
    (hB : B ≠ 0) :
    0 < (inner ℝ B (printedDeltaKOp D bc (Sof U) B) : ℝ) := by
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hmain := wired_coercive_uniform_in_U D bc Qext Jof Sof hS γ₁ c₂ R hc₂ hfloor hD2 hR U B
  have hgap : 0 < γ₁ - 2 * ‖solutionOperator D‖ * c₂ * R := by linarith
  have hprod := mul_pos hgap (pow_pos hn 2)
  linarith [hmain, hprod]

#print axioms wired_posDef_uniform_in_U

/-! ## §4 — the threshold in terms of the link deviation `δ`

Combining §2 and §3: the admissible `δ` is written down explicitly from the four constants. -/

/-- **THE `δ`-THRESHOLD.**  If the link deviation of the whole class satisfies
`2‖H₁‖c₂‖T‖√(2|Bond L|)·495·δ < γ₁`, then the printed `Δ_k` is positive definite at EVERY
configuration in the class, with the single constant of §3. -/
theorem wired_posDef_of_linkDev (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (T : BondFnL2 L →L[ℝ] H)
    (Sof : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L →
      (BondFnL2 L →L[ℝ] BondFnL2 L))
    (hS : ∀ U, IsSourceOperator D Qext (T (JsuTwo U)) (Sof U))
    (γ₁ c₂ δ : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hthr : 2 * ‖solutionOperator D‖ * c₂
      * (‖T‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ))) < γ₁)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hU : ∀ U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L, LinkDev δ U')
    (B : BondFnL2 L) (hB : B ≠ 0) :
    0 < (inner ℝ B (printedDeltaKOp D bc (Sof U) B) : ℝ) :=
  wired_posDef_uniform_in_U D bc Qext (fun U' => T (JsuTwo U')) Sof hS γ₁ c₂
    (‖T‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ))) hc₂ hfloor hD2
    (fun U' => norm_source_le_of_linkDev T U' (hU U')) hthr U B hB

#print axioms wired_posDef_of_linkDev

/-! ## §5 — ONE FULLY DISCHARGED INSTANCE: `γ₁` computed, not assumed

At `deltak_wiring`'s witness datum every constant of §3 is COMPUTED: `‖H₁‖ ≤ 1` (`H₁ = I`),
`c₂ = ‖v‖` (`D̃⁽²⁾(B) = ‖B‖²v`), and `γ₁ = 1/2 − a` (`(QG₁Q*)⁻¹ = (1/2)I`).  The only inputs are
`a < 1/2` and the link deviation.  This uses the `A`/`B` collapse (`T := id`), which
`DeltaKWiring.collapsed_Q_bijective` costs explicitly; it is a non-vacuity witness. -/

theorem bondData_opNorm_H1_le_one :
    ‖solutionOperator (bondData (L := L))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [bondData_H1]
  simp

theorem bondData_hD2 (v : BondFnL2 L) (B : BondFnL2 L) :
    ‖Dtilde2Shape (bondQext v) B‖ ≤ ‖v‖ * ‖B‖ ^ 2 := by
  rw [bondDtilde2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_of_eq (by ring)

theorem bondData_hfloor (bc : BaseConstant) (B : BondFnL2 L) :
    ((1 / 2 : ℝ) - usedAt bc 0) * ‖B‖ ^ 2
      ≤ (inner ℝ B (deltaKQuadOp (bondData (L := L)) bc B) : ℝ) := by
  rw [inner_deltaKQuadOp]
  have hC : (inner ℝ B ((bondData (L := L)).CompInv B) : ℝ) = (1 / 2 : ℝ) * ‖B‖ ^ 2 := by
    show (inner ℝ B ((1 / 2 : ℝ) • B) : ℝ) = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hC, real_inner_self_eq_norm_sq]
  exact le_of_eq (by ring)

/-- **END TO END.**  `a < 1/2`, a link deviation below the explicit threshold, and the printed
`C*Δ_kC` — with the source term instantiated at the SAME configuration `U` that parametrises the
printed subspace — is positive definite on `ℓ²(Λ̃)`.  Nothing is left as a hypothesis about the
covariance. -/
theorem bondData_wired_posDef (bc : BaseConstant) (v : BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hU : LinkDev δ U)
    (hsmall : 2 * ‖v‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ))
      < (1 / 2 : ℝ) - usedAt bc 0)
    {ell : ℕ} (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) (JsuTwo U) U ell Dinv w := by
  have hJ := norm_JsuTwo_le U hU
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hH1 := bondData_opNorm_H1_le_one (L := L)
  have hJn : (0 : ℝ) ≤ ‖JsuTwo U‖ := norm_nonneg _
  have hthr : 2 * ‖solutionOperator (bondData (L := L))‖ * ‖v‖ * ‖JsuTwo U‖
      < (1 / 2 : ℝ) - usedAt bc 0 := by
    have h1 : 2 * ‖solutionOperator (bondData (L := L))‖ * ‖v‖ * ‖JsuTwo U‖
        ≤ 2 * ‖v‖ * ‖JsuTwo U‖ := by
      have hkey : 0 ≤ (‖v‖ * ‖JsuTwo U‖) * (1 - ‖solutionOperator (bondData (L := L))‖) :=
        mul_nonneg (mul_nonneg hnv hJn) (by linarith)
      nlinarith [hkey]
    have h2 : 2 * ‖v‖ * ‖JsuTwo U‖
        ≤ 2 * ‖v‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ)) := by
      nlinarith [hJ, hnv]
    linarith
  exact cdcFormTrue_posDef_of_source_small (bondData (L := L)) bc (bondQext v) (JsuTwo U)
    ((inner ℝ v (JsuTwo U) : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
    (bondData_isSourceOperator v (JsuTwo U)) ((1 / 2 : ℝ) - usedAt bc 0) ‖v‖ hnv
    (bondData_hfloor bc) (bondData_hD2 v) hthr U Dinv w hw

#print axioms bondData_wired_posDef

/-! ## §6 — the wired source is NOT identically zero

A wiring that silently set `J := 0` would make everything above true and worthless.  It does not:
`SourceJ`'s own non-flat witness has `J(U) ≠ 0`, and the flat background has `J(U) = 0`, so the
lift separates configurations. -/

theorem JsuTwo_witnessU_ne_zero :
    JsuTwo AdalyFormal.Balaban.CovariantOperators.witnessU ≠ 0 := by
  intro h
  have hb : ((WithLp.ofLp (JsuTwo AdalyFormal.Balaban.CovariantOperators.witnessU)
      (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ)
      = Complex.I • AdalyFormal.Balaban.SourceJ.Jsource
          AdalyFormal.Balaban.CovariantOperators.witnessU
          (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) :=
    AdalyFormal.Balaban.SourceWiredJ.JsuTwo_apply _ _
  rw [h] at hb
  have hz : Complex.I • AdalyFormal.Balaban.SourceJ.Jsource
      AdalyFormal.Balaban.CovariantOperators.witnessU
      (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) = 0 := by
    rw [← hb]
    simp
  have : AdalyFormal.Balaban.SourceJ.Jsource AdalyFormal.Balaban.CovariantOperators.witnessU
      (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) = 0 := by
    have := congrArg (fun X => (Complex.I⁻¹ : ℂ) • X) hz
    simpa [smul_smul, Complex.inv_I] using this
  exact AdalyFormal.Balaban.SourceJ.Jsource_witnessU_ne_zero this

#print axioms JsuTwo_witnessU_ne_zero

end AdalyFormal.Balaban.SourceWired
