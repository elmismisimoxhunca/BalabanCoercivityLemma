/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import DeltaKWiring

set_option autoImplicit false

/-!
# THE THRESHOLD: CMP99b (3.156)'s printed `Δ_k` is coercive once the source is small

`compute/deltak_wiring/` proved (`cdcFormTrue_unbounded_below_in_J`,
`printed_cdc_not_posDef_general`) that the printed `C*Δ_kC` has NO lower bound uniform in a FREE
`J : H`.  That is a true theorem about a family `Δ_k(U,J)` with `J` an independent parameter.
CMP99b's `J` is not independent: p.392 (3.11) defines `J = D*η⁻²Im∂U`.

This module supplies the missing quantitative half: an EXPLICIT coercivity constant for the
printed three-summand form, composed from
* `γ₁` — a lower bound for the `J`-free part `(QG₁Q*)⁻¹ − a·I` (CMP99b's own support for this is
  *"[4], Lemma 2.4, for operators with `U = 1`"* — the LAW-12 deferred class; carried here as a
  named hypothesis, never assumed silently),
* `‖H₁‖` — the operator norm of `solutionOperator D`, which is a genuine `→L[ℝ]`,
* `c₂` — a bound `‖D̃⁽²⁾(B)‖ ≤ c₂‖B‖²`, which is exactly the content of CMP99b p.427's *"the
  function `D̃⁽²⁾(B)` is a quadratic polynomial in `B`"* on a finite-dimensional carrier,
* `‖J‖` — the size of the source.

The conclusion is `γ₀ = γ₁ − 2‖H₁‖c₂‖J‖`.  Nothing here decides whether `γ₁ > 0`; that is the
other half of the printed claim and is left NAMED.  What is decided here is the exact form of the
`J`-dependence: the printed form is coercive on the nose as soon as `2‖H₁‖c₂‖J‖ < γ₁`, so the
whole question of the source term is a SIZE question, not a structural one.

## The two directions, together

`deltak_wiring`'s `cdcFormTrue_unbounded_below_in_J` and this module's
`printedDeltaK_coercive_of_source_small` are the two halves of one sharp statement:
positivity fails for large `‖J‖` and holds for small `‖J‖`, at the SAME operator.  What decides
which regime CMP99b is in is whether the printed `J(U)` can be large — answered in
`SourceWiredJ.lean` (it cannot: its image is bounded, and it is `O(δ)` in the link deviation).
-/

namespace AdalyFormal.Balaban.SourceWired

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKAssembly (deltaKForm)
open AdalyFormal.Balaban.DeltaKWiring (sourceTerm deltaKQuadOp IsSourceOperator printedDeltaKOp
  inner_printedDeltaKOp inner_deltaKQuadOp cdcFormTrue norm_cZero_pos)

variable {L : PeriodicLatticeExtent}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## §1 — the source term is bounded by a product of FOUR counted factors

No constant is invented: `‖H₁‖` is the operator norm of an object already in the tree, `c₂` is a
hypothesis on `D̃⁽²⁾` whose referent is p.427's own sentence, `‖J‖` is the datum, `‖B‖²` is forced
by degree-2 homogeneity (`DeltaKWiring.sourceTerm_homog_of_isSourceOperator`). -/

/-- **`|⟨H₁D̃⁽²⁾(B),J⟩| ≤ ‖H₁‖·c₂·‖J‖·‖B‖²`** — Cauchy–Schwarz, the operator-norm bound for `H₁`,
and the quadratic bound on `D̃⁽²⁾`, in that order.  Each factor is separately named. -/
theorem abs_sourceTerm_le (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2) (B : BondFnL2 L) :
    |sourceTerm D Qext J B| ≤ ‖solutionOperator D‖ * c₂ * ‖J‖ * ‖B‖ ^ 2 := by
  have hcs : |sourceTerm D Qext J B|
      ≤ ‖solutionOperator D (Dtilde2Shape Qext B)‖ * ‖J‖ :=
    abs_real_inner_le_norm _ _
  have hop : ‖solutionOperator D (Dtilde2Shape Qext B)‖
      ≤ ‖solutionOperator D‖ * (c₂ * ‖B‖ ^ 2) := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    exact mul_le_mul_of_nonneg_left (hD2 B) (norm_nonneg _)
  refine le_trans hcs ?_
  have h := mul_le_mul_of_nonneg_right hop (norm_nonneg J)
  calc ‖solutionOperator D (Dtilde2Shape Qext B)‖ * ‖J‖
      ≤ ‖solutionOperator D‖ * (c₂ * ‖B‖ ^ 2) * ‖J‖ := h
    _ = ‖solutionOperator D‖ * c₂ * ‖J‖ * ‖B‖ ^ 2 := by ring

#print axioms abs_sourceTerm_le

/-! ## §2 — THE THRESHOLD THEOREM -/

/-- **THE PRINTED `Δ_k` IS COERCIVE WITH CONSTANT `γ₁ − 2‖H₁‖c₂‖J‖`.**

Every hypothesis is named and none is about `J`'s freedom:
* `hS` — `S` represents the source term (`DeltaKWiring.IsSourceOperator`, co-extensive with the
  existence of the printed `Δ_k` as an operator, by `printedDeltaK_exists_iff_source_isOperator`);
* `hfloor` — the `J`-FREE part `(QG₁Q*)⁻¹ − a·I` is bounded below by `γ₁` (CMP99b's own
  *"[4], Lemma 2.4"*, deferred there; NOT proved here, NOT assumed positive here);
* `hD2` — `D̃⁽²⁾` is quadratically bounded (p.427's *"quadratic polynomial in `B`"*).

The conclusion is an inequality at EVERY `B`, so no `γ₁ > 0` is needed for the statement to be
meaningful: it is an exact accounting of how much the source term can eat. -/
theorem printedDeltaK_coercive_of_source_small (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext J S)
    (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2) (B : BondFnL2 L) :
    (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖) * ‖B‖ ^ 2
      ≤ (inner ℝ B (printedDeltaKOp D bc S B) : ℝ) := by
  have hsplit : (inner ℝ B (printedDeltaKOp D bc S B) : ℝ)
      = (inner ℝ B (deltaKQuadOp D bc B) : ℝ) - 2 * sourceTerm D Qext J B := by
    show (inner ℝ B (deltaKQuadOp D bc B - (2 : ℝ) • S B) : ℝ) = _
    rw [inner_sub_right, real_inner_smul_right, hS B]
  have hsrc := abs_sourceTerm_le D Qext J c₂ hc₂ hD2 B
  have hsrc' : sourceTerm D Qext J B ≤ ‖solutionOperator D‖ * c₂ * ‖J‖ * ‖B‖ ^ 2 :=
    le_trans (le_abs_self _) hsrc
  rw [hsplit]
  have := hfloor B
  nlinarith [this, hsrc']

#print axioms printedDeltaK_coercive_of_source_small

/-- **STRICT POSITIVE DEFINITENESS**, the form the printed claim asserts: below the threshold
`2‖H₁‖c₂‖J‖ < γ₁` the printed `Δ_k` is positive definite. -/
theorem printedDeltaK_posDef_of_source_small (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext J S)
    (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hthr : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < γ₁)
    (B : BondFnL2 L) (hB : B ≠ 0) :
    0 < (inner ℝ B (printedDeltaKOp D bc S B) : ℝ) := by
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hmain := printedDeltaK_coercive_of_source_small D bc Qext J S hS γ₁ c₂ hc₂ hfloor hD2 B
  have hgap : 0 < γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ := by linarith
  have hsq : 0 < ‖B‖ ^ 2 := pow_pos hn 2
  have hprod := mul_pos hgap hsq
  linarith [hmain, hprod]

#print axioms printedDeltaK_posDef_of_source_small

/-! ## §3 — the same statement at the COMPRESSED operator `C*Δ_kC`, on the printed subspace

`cdcFormTrue` is `deltak_wiring`'s own compression of the printed form by `construct_cdc`'s `C₀`
(whose image lies in the printed subspace, `DeltaKWiring.cZero_in_printed_subspace`).  This is the
object CMP99b p.428's `γ₀` sentence is about. -/

/-- **`C*Δ_kC ≥ (γ₁ − 2‖H₁‖c₂‖J‖)·‖C₀B̃‖²`.**  The compressed printed form inherits the threshold
verbatim; nothing about `C₀` enters the constant. -/
theorem cdcFormTrue_coercive_of_source_small (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext J S)
    (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) :
    (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖) * ‖cZero U ell Dinv w‖ ^ 2
      ≤ cdcFormTrue D bc Qext J U ell Dinv w := by
  have h := printedDeltaK_coercive_of_source_small D bc Qext J S hS γ₁ c₂ hc₂ hfloor hD2
    (cZero U ell Dinv w)
  have he := inner_printedDeltaKOp D bc Qext J S hS (cZero U ell Dinv w)
  show _ ≤ deltaKForm D bc Qext J (cZero U ell Dinv w)
  rw [← he]
  exact h

#print axioms cdcFormTrue_coercive_of_source_small

/-- **THE PRINTED `C*Δ_kC` IS POSITIVE DEFINITE ON `ℓ²(Λ̃)` BELOW THE THRESHOLD.**  This is the
`γ₀` sentence's own conclusion, with `γ₀` exhibited and the source's contribution accounted. -/
theorem cdcFormTrue_posDef_of_source_small (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext J S)
    (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ))
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hthr : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < γ₁)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell Dinv w := by
  have hpos : 0 < ‖cZero U ell Dinv w‖ := norm_cZero_pos U Dinv w hw
  have h := cdcFormTrue_coercive_of_source_small D bc Qext J S hS γ₁ c₂ hc₂ hfloor hD2 U Dinv w
  have hgap : 0 < γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ := by linarith
  have hsq : 0 < ‖cZero U ell Dinv w‖ ^ 2 := pow_pos hpos 2
  have hprod := mul_pos hgap hsq
  linarith [h, hprod]

#print axioms cdcFormTrue_posDef_of_source_small

/-! ## §4 — the threshold, solved for `‖J‖`

The three named constants determine an explicit admissible source size.  Stated as a separate
theorem so a consumer can read off exactly which quantity must be small. -/

/-- **THE ADMISSIBLE SOURCE SIZE.**  If `‖J‖ < γ₁ / (2‖H₁‖c₂)` (with the denominator positive)
then the threshold hypothesis of `printedDeltaK_posDef_of_source_small` holds. -/
theorem threshold_of_norm_J_lt (D : BalabanCovarianceData H (BondFnL2 L)) (J : H) (γ₁ c₂ : ℝ)
    (hden : 0 < 2 * ‖solutionOperator D‖ * c₂)
    (hJ : ‖J‖ < γ₁ / (2 * ‖solutionOperator D‖ * c₂)) :
    2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < γ₁ := by
  have h := (lt_div_iff₀ hden).mp hJ
  have hcomm : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖
      = ‖J‖ * (2 * ‖solutionOperator D‖ * c₂) := by ring
  rw [hcomm]
  exact h

#print axioms threshold_of_norm_J_lt

end AdalyFormal.Balaban.SourceWired
