/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawFeed
import QSurjGeneralCore

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `TerminalBinder.lean` — THE TERMINAL THEOREM'S BINDER, WEAKENED TO THE POINTS ITS PROOF USES

`TerminalAssembly.terminal_wired_posDef` carries the analytic input

    hraw : ∀ A : Hs, ‖D_U (Q A)‖ ≤ σ₀‖d A‖ + κ‖Q A‖

as a UNIVERSAL binder.  `HrawCarriers.hraw_composed_at_minimizer` proves that shape at a GENERAL
fine background but only on the range of `H₁ = solutionOperator D`.  The two do not meet.

## §0 — THE AUDIT, STATED SO IT CAN BE CHECKED AGAINST THE SOURCE

Reading `compute/terminal_assembly/stage/TerminalAssembly.lean`'s proofs, `hraw` is APPLIED exactly
once in the whole chain:

| declaration | line | what it does with `hraw` |
|---|---|---|
| `terminal_wired_posDef` | 887 | passes it through unapplied (line 937) |
| `terminal_posDef_of_source_bound` | 1173 | passes it through unapplied (line 1198) |
| `terminal_printed_posDef` | 772 | passes it through unapplied (line 789) |
| `schur_floor_hraw_at_cZero` | 601 | **applies it, once**, at line 618: `(hraw A)` where lines 614–615 `set B := cZero U ell (dinvC U ell) w`, `set A := solutionOperator D B` |

So the consumed value is `H₁ (C₀B̃)`, a point of the minimiser range.  `hform` (CMP99b (3.128)) is
consumed at the SAME single point (line 620) and nowhere else, so it is weakened here by the
identical move — a second, unasked weakening.

**This module does not edit `compute/terminal_assembly/` or `compute/hraw_carriers/` (LAW-4).**
Every upstream theorem is imported and reused; the restatements below are new declarations.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.TerminalBinder

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  interpolates isMinimal)
open AdalyFormal.Balaban.Gamma1Positive (IsAQuadSplit deltaKQuadForm deltaKQuadForm_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue deltaKQuadOp)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.TerminalAssembly (IsPrintedG1Form canonicalKop inner_canonicalKop
  canonical_isAQuadSplit sharpFloorConst floor_of_hraw_sharp hpoin_at_cZero
  cdcFormTrue_posDef_at_cZero deltaKQuadForm_eq_inner_deltaKQuadOp sharpFloorConst_lower_halfDrift
  delta_threshold_suffices)
open AdalyFormal.Balaban.SourceWired (norm_source_le_of_linkDev)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {Ks : Type*} [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]
variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE TWO BINDERS, POINTWISE AND ON THE MINIMISER RANGE -/

/-- **CMP99b (3.128) AT ONE VECTOR.**  Character for character the body of
`TerminalAssembly.IsPrintedG1Form`, with the `∀ A` stripped. -/
def PrintedG1FormAt {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs Ks) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (A : Hs) : Prop :=
  (inner ℝ A (D.Ginv A) : ℝ) = ‖d A‖ ^ 2 + ‖pen A‖ ^ 2 + a * ‖D.Q A‖ ^ 2

/-- **THE DRIFT-PRICED CHAIN BOUND AT ONE VECTOR.**  Character for character the body of
`terminal_wired_posDef`'s `hraw` binder, with the `∀ A` stripped. -/
def HrawAt {P₁ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    (D : BalabanCovarianceData Hs (BondFnL2 L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Hs →L[ℝ] P₁) (σ₀ κ : ℝ) (A : Hs) : Prop :=
  ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖

/-- **THE UNIVERSAL BINDERS ARE THE POINTWISE ONES, QUANTIFIED** — so the weakenings below are
weakenings of exactly the upstream hypotheses and not of some paraphrase.  Both are `Iff.rfl`. -/
theorem isPrintedG1Form_iff {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs Ks) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃) :
    IsPrintedG1Form D a d pen ↔ ∀ A : Hs, PrintedG1FormAt D a d pen A := Iff.rfl

theorem hraw_iff {P₁ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    (D : BalabanCovarianceData Hs (BondFnL2 L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Hs →L[ℝ] P₁) (σ₀ κ : ℝ) :
    (∀ A : Hs, ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
      ↔ ∀ A : Hs, HrawAt D U d σ₀ κ A := Iff.rfl

/-- **THE MINIMISER RANGE**, named: the set of values of `H₁ = solutionOperator D`. -/
def OnMinimizerRange (D : BalabanCovarianceData Hs Ks) (P : Hs → Prop) : Prop :=
  ∀ B : Ks, P (solutionOperator D B)

/-- Specialisation: a universal hypothesis gives the minimiser-range one.  This is the direction
that makes the weakening LOSSLESS, and it is the only direction that is free. -/
theorem onMinimizerRange_of_forall (D : BalabanCovarianceData Hs Ks) (P : Hs → Prop)
    (h : ∀ A : Hs, P A) : OnMinimizerRange D P := fun B => h _

/-! ### §1a — THE WEAKENING IS STRICT: THE MINIMISER RANGE MISSES EVERY NON-ZERO KERNEL VECTOR

`H₁` is a right inverse section of `Q` (`interpolates`), so a vector killed by `Q` can be in its
range only if it is `0`.  When `Q` is not injective — which is the situation at the composed
carriers, `HrawCarriers.composedQ_not_injective`, CITED — the range is therefore a PROPER subset and
the quantifier weakening is not cosmetic. -/

/-- **THE RANGE MISSES THE KERNEL.**  If `A ≠ 0` and `Q A = 0` then `A` is not `H₁ B` for any `B`. -/
theorem minimizer_range_misses_kernel (D : BalabanCovarianceData Hs Ks) (A : Hs) (hA : A ≠ 0)
    (hQA : D.Q A = 0) (B : Ks) : solutionOperator D B ≠ A := by
  intro hEq
  have hB : B = 0 := by
    have h1 : D.Q (solutionOperator D B) = B := interpolates D B
    rw [hEq, hQA] at h1
    exact h1.symm
  rw [hB, map_zero] at hEq
  exact hA hEq.symm

/-- **THE QUANTIFIER WEAKENING IS STRICT WHENEVER THE RANGE IS PROPER.**  Given ONE vector outside
the range, there is a predicate that holds on the whole range and fails somewhere — so
`OnMinimizerRange D P` is strictly weaker than `∀ A, P A` as a hypothesis, i.e. the restated
theorems below genuinely apply in cases the originals do not.  The predicate is the indicator of the
missing vector; no property of `Q`, `Ginv` or the lattice is used. -/
theorem onMinimizerRange_strictly_weaker (D : BalabanCovarianceData Hs Ks) (A₀ : Hs)
    (hout : ∀ B : Ks, solutionOperator D B ≠ A₀) :
    ∃ P : Hs → Prop, OnMinimizerRange D P ∧ ¬ (∀ A : Hs, P A) := by
  classical
  refine ⟨fun A => A ≠ A₀, fun _B => hout _B, ?_⟩
  intro hall
  exact (hall A₀) rfl

/-! ### §1b — WHAT THE WEAKENING DOES **NOT** BUY, PROVED SO IT CANNOT BE OVERSOLD

The universal `hraw` binder is never EMPTY: it holds at every datum and every background with
`κ = ‖D_U‖` (the operator norm of the covariant curl) and any `σ₀ ≥ 0`.  So the obstruction at a
general fine background is never "the universal statement is false"; it is the SIZE of `κ`, which
`terminal_wired_posDef` constrains by `κ ≤ ½√(gammaBrick ℓ)`.  What the weakening buys is a SMALL
`κ` at a general fine background, which §3 supplies. -/
theorem hraw_universal_holds_at_opNorm {P₁ : Type*} [NormedAddCommGroup P₁]
    [InnerProductSpace ℝ P₁] (D : BalabanCovarianceData Hs (BondFnL2 L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Hs →L[ℝ] P₁) (σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀) (A : Hs) :
    HrawAt D U d σ₀ ‖curlCovariantCLM_L2 (L := L) U‖ A := by
  have h1 : ‖curlCovariantCLM_L2 U (D.Q A)‖
      ≤ ‖curlCovariantCLM_L2 (L := L) U‖ * ‖D.Q A‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : (0 : ℝ) ≤ σ₀ * ‖d A‖ := mul_nonneg hσ₀ (norm_nonneg _)
  show ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + _ * ‖D.Q A‖
  linarith

/-! ## §2 — THE SCHUR FLOOR AND THE TERMINAL CHAIN, RESTATED ON THE MINIMISER RANGE -/

/-- Pointwise `hKcurl`: `‖dA‖² ≤ ⟨A, Kop A⟩` from (3.128) AT `A` alone.  The upstream
`TerminalAssembly.hKcurl_of_printedG1Form` consumes the universal form; its proof uses only `hform A`
(it is `rw [inner_canonicalKop, hform A]`), so this is that proof with the binder removed. -/
theorem hKcurl_at {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    {D : BalabanCovarianceData Hs Ks} {a : ℝ} {d : Hs →L[ℝ] P₁} {pen : Hs →L[ℝ] P₃} {A : Hs}
    (hAt : PrintedG1FormAt D a d pen A) :
    ‖d A‖ ^ 2 ≤ (inner ℝ A (canonicalKop D a A) : ℝ) := by
  rw [inner_canonicalKop]
  have h : (inner ℝ A (D.Ginv A) : ℝ) = ‖d A‖ ^ 2 + ‖pen A‖ ^ 2 + a * ‖D.Q A‖ ^ 2 := hAt
  rw [h]
  nlinarith [sq_nonneg ‖pen A‖]

/-- **THE SCHUR FLOOR, WITH BOTH CARRIED HYPOTHESES AT THE SINGLE CONSUMED POINT.**

Statement, constant and conclusion are `TerminalAssembly.schur_floor_hraw_at_cZero`'s, unchanged.
The only change is that `hform` and `hraw` are required at `H₁(C₀B̃)` instead of everywhere. -/
theorem schur_floor_at_point {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaBrick ell))
    (w : TildeFn L ell)
    (hformAt : PrintedG1FormAt D a d pen (solutionOperator D (cZero U ell (dinvC U ell) w)))
    (hrawAt : HrawAt D U d σ₀ κ (solutionOperator D (cZero U ell (dinvC U ell) w))) :
    sharpFloorConst (gammaBrick ell) κ σ₀ * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) := by
  set B : BondFnL2 L := cZero U ell (dinvC U ell) w with hB
  set A : Hs := solutionOperator D B with hA
  have hQA : D.Q A = B := interpolates D B
  have hfl := floor_of_hraw_sharp D.Q d (curlCovariantCLM_L2 U) (canonicalKop D a) σ₀ κ
    (gammaBrick ell) hσ₀ hκ hκγ A hrawAt
    (by rw [hQA]; exact hpoin_at_cZero hell2 hstrict hdvd U hthr w)
    (hKcurl_at hformAt)
  rw [hQA] at hfl
  rw [deltaKQuadForm_eq D a (canonicalKop D a) (canonical_isAQuadSplit D a) B]
  exact hfl

/-- **THE SCHUR FLOOR ON THE MINIMISER RANGE.**  The usable packaging: both hypotheses quantified
over `B`, i.e. over the range of `H₁`, which is the shape `hraw_composed_at_minimizer` delivers. -/
theorem schur_floor_on_range {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaBrick ell))
    (hformR : OnMinimizerRange D (PrintedG1FormAt D a d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (w : TildeFn L ell) :
    sharpFloorConst (gammaBrick ell) κ σ₀ * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) :=
  schur_floor_at_point hell2 hstrict hdvd U hthr D a d pen σ₀ κ hσ₀ hκ hκγ w
    (hformR _) (hrawR _)

/-- **NOTHING IS LOST — `schur_floor_hraw_at_cZero`'S EXACT STATEMENT, RECOVERED.**  Signature and
conclusion copied from `TerminalAssembly.schur_floor_hraw_at_cZero`; the proof feeds the universal
hypotheses to the weakened theorem.  If a single binder had drifted this would not typecheck. -/
theorem schur_floor_hraw_at_cZero_recovered {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (a : ℝ) (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (hform : IsPrintedG1Form D a d pen) (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ)
    (hκγ : κ ≤ Real.sqrt (gammaBrick ell))
    (hraw : ∀ A : Hs, ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
    (w : TildeFn L ell) :
    sharpFloorConst (gammaBrick ell) κ σ₀ * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) :=
  schur_floor_on_range hell2 hstrict hdvd U hthr D a d pen σ₀ κ hσ₀ hκ hκγ
    (fun B => hform (solutionOperator D B)) (fun B => hraw (solutionOperator D B)) w

/-! ### §2a — THE COMPOSED THEOREM AND THE HEADLINE, ON THE MINIMISER RANGE -/

/-- `terminal_printed_posDef` with both covariance-side binders on the minimiser range. -/
theorem terminal_printed_posDef_on_range {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaBrick ell))
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hsmall : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < sharpFloorConst (gammaBrick ell) κ σ₀)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  have hfl := schur_floor_on_range hell2 hstrict hdvd U hthr D (usedAt bc 0) d pen σ₀ κ hσ₀ hκ hκγ
    hformR hrawR w
  rw [deltaKQuadForm_eq_inner_deltaKQuadOp D bc] at hfl
  exact cdcFormTrue_posDef_at_cZero D bc Qext J S hS _ c₂ hc₂ hD2 U (dinvC U ell) w hw hfl hsmall

/-- `terminal_posDef_of_source_bound` (§10a upstream) on the minimiser range: the source enters only
through a bound `‖J‖ ≤ R`, so either supplier (global gauge or the printed per-cube class) feeds it. -/
theorem terminal_posDef_of_source_bound_on_range {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaBrick ell) / 2)
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator D‖ * c₂ * R < sharpFloorConst (gammaBrick ell) κ σ₀)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt (gammaBrick ell) := Real.sqrt_nonneg _
  have hκγ : κ ≤ Real.sqrt (gammaBrick ell) := by linarith
  have hcoef : (0 : ℝ) ≤ 2 * ‖solutionOperator D‖ * c₂ := by positivity
  have hsmall : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖
      < sharpFloorConst (gammaBrick ell) κ σ₀ := by
    have := mul_le_mul_of_nonneg_left hJbound hcoef
    linarith
  exact terminal_printed_posDef_on_range hell2 hstrict hdvd U hthr D bc d pen σ₀ κ hσ₀ hκ hκγ
    hformR hrawR Qext J S hS c₂ hc₂ hD2 hsmall w hw

/-- **THE HEADLINE ON THE MINIMISER RANGE.**  `terminal_wired_posDef` with `hform` and `hraw`
required only at the values of `H₁`.  Everything else — the `δ` threshold in exact rationals, the
half-drift hypothesis, the source wiring — is copied unchanged and the arithmetic is the upstream
lane's, reused (`delta_threshold_suffices`, `sharpFloorConst_lower_halfDrift`,
`norm_source_le_of_linkDev`). -/
theorem terminal_wired_posDef_on_range {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaBrick ell) / 2)
    (hformR : OnMinimizerRange D (PrintedG1FormAt D (usedAt bc 0) d pen))
    (hrawR : OnMinimizerRange D (HrawAt D U d σ₀ κ))
    (Qext : BondFnL2 L → BondFnL2 L) (T : BondFnL2 L →L[ℝ] Hs)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator D‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L))
    (hδ : δ < 1 / (1370001600 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * ‖solutionOperator D‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L))))))
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext (T (JsuTwo U)) U ell (dinvC U ell) w := by
  have hell : 0 < ell := by omega
  set N : ℝ := Real.sqrt (2 * (Fintype.card (Bond L))) with hN
  have hNpos : 0 < N := by
    rw [hN]
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (Fintype.card (Bond L) : ℝ) := by exact_mod_cast hcard
    linarith
  have hJ : ‖T (JsuTwo U)‖ ≤ ‖T‖ * (N * (495 * δ)) := norm_source_le_of_linkDev T U hU
  have harith : 2 * ‖solutionOperator D‖ * c₂ * ((‖T‖ * N) * (495 * δ))
      < 1 / (1383840 * (ell : ℝ) ^ 6 * σ₀ ^ 2) :=
    delta_threshold_suffices hell σ₀ ‖solutionOperator D‖ c₂ (‖T‖ * N) δ hσ₀ hH1 hc₂
      (by positivity) hδ0 (by rw [hN] at hδ ⊢; exact hδ)
  have hγlow : 1 / (1383840 * (ell : ℝ) ^ 6 * σ₀ ^ 2)
      ≤ sharpFloorConst (gammaBrick ell) κ σ₀ :=
    sharpFloorConst_lower_halfDrift hell σ₀ κ hσ₀ hκ hhalf
  have hcoef : (0 : ℝ) ≤ 2 * ‖solutionOperator D‖ * c₂ := by positivity
  have hstep : 2 * ‖solutionOperator D‖ * c₂ * ‖T (JsuTwo U)‖
      ≤ 2 * ‖solutionOperator D‖ * c₂ * ((‖T‖ * N) * (495 * δ)) := by
    have hre : ‖T‖ * (N * (495 * δ)) = (‖T‖ * N) * (495 * δ) := by ring
    rw [← hre]
    exact mul_le_mul_of_nonneg_left hJ hcoef
  have hRthr : 2 * ‖solutionOperator D‖ * c₂ * ‖T (JsuTwo U)‖
      < sharpFloorConst (gammaBrick ell) κ σ₀ := by linarith
  exact terminal_posDef_of_source_bound_on_range hell2 hstrict hdvd U hthr D bc d pen σ₀ κ hσ₀ hκ
    hhalf hformR hrawR Qext (T (JsuTwo U)) S hS c₂ (le_of_lt hc₂) hD2 ‖T (JsuTwo U)‖ le_rfl hRthr
    w hw

/-- **NOTHING IS LOST — `terminal_wired_posDef`'S EXACT STATEMENT, RECOVERED.**  Every binder copied
from `TerminalAssembly.terminal_wired_posDef` (lines 887–909); the proof is the specialisation of the
two universal hypotheses to the minimiser range.  This is the `mech_edges` losslessness pattern
(`gamma_floor_at_minimizer_from_pointwise`) applied one level up. -/
theorem terminal_wired_posDef_recovered {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (hform : IsPrintedG1Form D (usedAt bc 0) d pen)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ)
    (hhalf : κ ≤ Real.sqrt (gammaBrick ell) / 2)
    (hraw : ∀ A : Hs, ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
    (Qext : BondFnL2 L → BondFnL2 L) (T : BondFnL2 L →L[ℝ] Hs)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator D‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L))
    (hδ : δ < 1 / (1370001600 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * ‖solutionOperator D‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L))))))
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext (T (JsuTwo U)) U ell (dinvC U ell) w :=
  terminal_wired_posDef_on_range hell2 hstrict hdvd U hthr D bc d pen σ₀ κ hσ₀ hκ hhalf
    (fun B => hform (solutionOperator D B)) (fun B => hraw (solutionOperator D B))
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

#print axioms PrintedG1FormAt
#print axioms HrawAt
#print axioms isPrintedG1Form_iff
#print axioms hraw_iff
#print axioms OnMinimizerRange
#print axioms onMinimizerRange_of_forall
#print axioms minimizer_range_misses_kernel
#print axioms onMinimizerRange_strictly_weaker
#print axioms hraw_universal_holds_at_opNorm
#print axioms hKcurl_at
#print axioms schur_floor_at_point
#print axioms schur_floor_on_range
#print axioms schur_floor_hraw_at_cZero_recovered
#print axioms terminal_printed_posDef_on_range
#print axioms terminal_posDef_of_source_bound_on_range
#print axioms terminal_wired_posDef_on_range
#print axioms terminal_wired_posDef_recovered

end AdalyFormal.TerminalBinder

namespace AdalyFormal.TerminalBinder

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator interpolates)
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM dstarDLM inner_dstarDLM_symm)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.TerminalAssembly (IsPrintedG1Form sharpFloorConst
  normSq_curlCLM_eq_dstarDCLM_form norm_solutionOperator_le_of_lift)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos rawErrorCoeff rawErrorCoeff_nonneg)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale dvd_of_scale coarseFnL2Equiv
  composedQ composedQ_apply composedQ_not_injective hraw_composed_at_minimizer
  feedPen norm_feedPen_sq sqrt_two_le sqrt_gammaBrick_lower rawErrorCoeff_trivialU)
open AdalyFormal.HBaseInputs.CovData (build build_Q build_Ginv)

variable {L L' : PeriodicLatticeExtent}

/-! ## §3 — THE FEED: A DATUM AT A **GENERAL** FINE BACKGROUND, ON THE COMPOSED CARRIERS

`HrawFeed.feedDatum` is built at the FLAT fine background (`composedQ h (trivialU L)`), because
`HrawCarriers.composedQ_surjective` — the input `CovDataCtor.build` demands — was proved only there.
§3a lifts that to an ARBITRARY fine background using `QSurjCriterion.qCLM_surjective_general`
(the `compute/qsurj_criterion/` lane's unconditional-in-`U` surjectivity, CITED and REUSED, staged
here as `dep/QSurjGeneralCore.lean`, a verbatim subset of that lane's file — see `QSURJ_TRIM.diff`).

Then `hraw_composed_at_minimizer`, which needs no flatness anywhere, discharges the weakened binder
of §2, and the terminal positivity holds at a general fine background. -/

/-- **§3a — `composedQ` IS SURJECTIVE AT EVERY FINE BACKGROUND.**  `HrawCarriers.composedQ_surjective`
with `qCLM_surjective_trivialU` replaced by `qCLM_surjective_general`; the extent identification is
an equivalence, so the composite is surjective. -/
theorem composedQ_surjective_gen {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Function.Surjective (composedQ h Ufine) := by
  intro y
  obtain ⟨x, hx⟩ := QSurjCriterion.qCLM_surjective_general Ufine (ell_pos_of_scale h)
    (dvd_of_scale h) ((coarseFnL2Equiv h).symm y)
  refine ⟨x, ?_⟩
  rw [composedQ_apply, hx]
  exact (coarseFnL2Equiv h).apply_symm_apply y

/-- `G₁⁻¹ := D_{U_fine}^*D_{U_fine} + ε·I + a·Q^*Q` at a GENERAL fine background.  Same three
summands as `HrawFeed.feedGinv`, with `trivialU L` replaced by `Ufine` throughout. -/
noncomputable def feedGinvGen {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  dstarDCLM Ufine + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
    + a • ((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp (composedQ h Ufine))

theorem inner_feedGinvGen {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (A : BondFnL2 L) :
    (inner ℝ A (feedGinvGen h Ufine eps a A) : ℝ)
      = ‖curlCovariantCLM_L2 Ufine A‖ ^ 2 + eps * ‖A‖ ^ 2
        + a * ‖composedQ h Ufine A‖ ^ 2 := by
  show (inner ℝ A ((dstarDCLM Ufine + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
    + a • ((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
      (composedQ h Ufine))) A) : ℝ) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, inner_add_right, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, real_inner_smul_right,
    real_inner_smul_right]
  have hQ : (inner ℝ A (((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
      (composedQ h Ufine)) A) : ℝ) = ‖composedQ h Ufine A‖ ^ 2 := by
    show (inner ℝ A (ContinuousLinearMap.adjoint (composedQ h Ufine)
      (composedQ h Ufine A)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hQ, normSq_curlCLM_eq_dstarDCLM_form Ufine A]
  show (inner ℝ A (dstarDCLM Ufine A) : ℝ) + eps * (inner ℝ A A : ℝ) + _ = _
  rw [real_inner_self_eq_norm_sq]

theorem feedGinvGen_selfAdjoint {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (x y : BondFnL2 L) :
    (inner ℝ (feedGinvGen h Ufine eps a x) y : ℝ) = inner ℝ x (feedGinvGen h Ufine eps a y) := by
  show (inner ℝ ((dstarDCLM Ufine + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
      + a • ((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
        (composedQ h Ufine))) x) y : ℝ)
    = inner ℝ x ((dstarDCLM Ufine + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
      + a • ((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
        (composedQ h Ufine))) y)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
  have hd : (inner ℝ (dstarDCLM Ufine x) y : ℝ) = inner ℝ x (dstarDCLM Ufine y) := by
    show (inner ℝ (dstarDLM Ufine x) y : ℝ) = inner ℝ x (dstarDLM Ufine y)
    rw [inner_dstarDLM_symm]
  have hQ : (inner ℝ (((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
        (composedQ h Ufine)) x) y : ℝ)
      = inner ℝ x (((ContinuousLinearMap.adjoint (composedQ h Ufine)).comp
        (composedQ h Ufine)) y) := by
    show (inner ℝ (ContinuousLinearMap.adjoint (composedQ h Ufine)
        (composedQ h Ufine x)) y : ℝ)
      = inner ℝ x (ContinuousLinearMap.adjoint (composedQ h Ufine)
        (composedQ h Ufine y))
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  simp only [hd, hQ, ContinuousLinearMap.id_apply]

theorem feedGinvGen_posDef {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (x : BondFnL2 L) (hx : x ≠ 0) :
    (0 : ℝ) < inner ℝ x (feedGinvGen h Ufine eps a x) := by
  rw [inner_feedGinvGen]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : (0 : ℝ) ≤ ‖curlCovariantCLM_L2 Ufine x‖ ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ a * ‖composedQ h Ufine x‖ ^ 2 := mul_nonneg ha (sq_nonneg _)
  nlinarith [mul_pos heps (pow_pos hn 2)]

/-- **THE DATUM AT A GENERAL FINE BACKGROUND.** -/
noncomputable def feedDatumGen {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    BalabanCovarianceData (BondFnL2 L) (BondFnL2 L') :=
  build (feedGinvGen h Ufine eps a) (composedQ h Ufine) (feedGinvGen_selfAdjoint h Ufine eps a)
    (feedGinvGen_posDef h Ufine heps ha) (composedQ_surjective_gen h Ufine)

theorem feedDatumGen_Q {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    (feedDatumGen h Ufine heps ha).Q = composedQ h Ufine := rfl

theorem feedDatumGen_Ginv {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    (feedDatumGen h Ufine heps ha).Ginv = feedGinvGen h Ufine eps a := rfl

/-- **(3.128) HOLDS AT THE GENERAL-FINE DATUM, AS AN EQUALITY**, with `d = ∂_{U_fine}` the covariant
coboundary at the SAME fine background, `pen = √ε·I` and the same `a`.  Universal in `A`, so the
weakened binder of §2 is fed a fortiori. -/
theorem feedDatumGen_isPrintedG1Form {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    IsPrintedG1Form (feedDatumGen h Ufine heps ha) a (curlCovariantCLM_L2 Ufine)
      (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L) := by
  intro A
  rw [feedDatumGen_Ginv h Ufine heps ha, inner_feedGinvGen,
    norm_feedPen_sq (le_of_lt heps) A]
  rw [feedDatumGen_Q h Ufine heps ha]

/-- **THE WEAKENED `hraw` BINDER IS A THEOREM AT THE GENERAL-FINE DATUM.**  This is the pairing the
lane was dispatched for: `hraw_composed_at_minimizer` (general fine background, minimiser range
only) lands exactly in `OnMinimizerRange … (HrawAt …)`.

`σ₀ = ℓ^{-1/2}`; `κ = 4√2·α₁(U) + ‖H₁‖·(36√2·ℓ^{-1/2})·α₁(U_fine)`. -/
theorem feedDatumGen_hraw_on_range {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L') :
    OnMinimizerRange (feedDatumGen h Ufine heps ha)
      (HrawAt (feedDatumGen h Ufine heps ha) U (curlCovariantCLM_L2 Ufine) (rawSigmaZero ell)
        (4 * Real.sqrt 2 * frobSupBond U
          + ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ * rawErrorCoeff ell Ufine)) :=
  fun B => hraw_composed_at_minimizer h (feedDatumGen h Ufine heps ha) Ufine
    (feedDatumGen_Q h Ufine heps ha) U B

/-! ### §3b — THE SMALLNESS, SPLIT INTO TWO COUNTED PIECES

`terminal_wired_posDef_on_range` needs `κ ≤ ½√(gammaBrick ℓ₀)`.  §3b splits that between the two
backgrounds.  Every constant is derived, none fitted:

* `√(gammaBrick ℓ₀) ≥ 1/(589·ℓ₀³)` — `HrawCarriers.sqrt_gammaBrick_lower`, CITED (`589² = 346921 ≥ 345960`);
* `√2 ≤ 1.4143` — `HrawCarriers.sqrt_two_le`, CITED (`1.4143² = 2.00024449 ≥ 2`);
* `2356 = 4·589`, so `1/(2356·ℓ₀³) = ¼·1/(589·ℓ₀³)`;
* `13336 = 2·6668`, and `4·1.4143·2356 = 13328.36 ≤ 13336`, which is why the coarse smallness is
  EXACTLY twice as tight as `HrawFeed`'s `1/(6668·ℓ₀³)` — the extra factor `2` is the half of the
  budget that the FINE background's drift now consumes. -/
theorem halfDrift_split {ell₀ : ℕ} (hell : 0 < ell₀) (x y : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3))
    (hy : y ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * x + y ≤ Real.sqrt (gammaBrick ell₀) / 2 := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  have hs := sqrt_two_le
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hg := sqrt_gammaBrick_lower hell
  have hstep1 : 4 * Real.sqrt 2 * x ≤ 4 * 1.4143 * (1 / (13336 * (ell₀ : ℝ) ^ 3)) := by
    have hA : 4 * Real.sqrt 2 ≤ 4 * 1.4143 := by linarith
    have hB : (0 : ℝ) ≤ 4 * Real.sqrt 2 := by positivity
    nlinarith [hx, hx0, hA, hB]
  have hstep2 : 4 * 1.4143 * (1 / (13336 * (ell₀ : ℝ) ^ 3)) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
    have hL : 4 * 1.4143 * (1 / (13336 * (ell₀ : ℝ) ^ 3))
        = (4 * 1.4143) / (13336 * (ell₀ : ℝ) ^ 3) := by ring
    rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp3]
  have hsum : 4 * Real.sqrt 2 * x + y ≤ 2 * (1 / (2356 * (ell₀ : ℝ) ^ 3)) := by linarith
  have hhalf : 2 * (1 / (2356 * (ell₀ : ℝ) ^ 3)) = (1 / (589 * (ell₀ : ℝ) ^ 3)) / 2 := by
    field_simp
    ring
  rw [hhalf] at hsum
  linarith

/-- `13336 > 186`, so the coarse smallness of §3b implies the printed `(3.35)` class membership
`hthr` and it is not a second, independent hypothesis. -/
theorem thirteen336_strictly_smaller {ell₀ : ℕ} (hell : 0 < ell₀) :
    1 / (13336 * (ell₀ : ℝ) ^ 3) < 1 / (186 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hp]

/-! ## §4 — **THE TERMINAL POSITIVITY AT A GENERAL FINE BACKGROUND** -/

/-- **THE RESULT THIS LANE WAS DISPATCHED FOR.**

    ℓ₀ ≥ 2, tiled torus on `L'`,  α₁(U) ≤ 1/(13336·ℓ₀³),
    ‖H₁‖·α₁(U_fine)·(36√2/√ℓ)  ≤ 1/(2356·ℓ₀³),
    δ < 1/(1370001600·ℓ₀⁶·σ₀²·‖H₁‖·c₂·(‖T‖√(2|Bond L'|)))
    ⟹  ⟨B̃, C*Δ_k(U)C B̃⟩ > 0   for every B̃ ≠ 0 in ℓ²(Λ̃).

Compared with `HrawFeed.terminal_at_composed_carriers`, **the fine background `U_fine` is now
ARBITRARY** — that lane's statement is at `trivialU L`.  The price is exactly the second smallness
line, whose coefficient is the fine drift `rawErrorCoeff ℓ U_fine` weighted by `‖H₁‖`, and which is
`0` at `U_fine = 1` (§5a).

**Hypothesis inventory, tagged.**
* `hell2`, `hstrict`, `hdvd0` — [OURS] tiling conditions on the COARSE torus `L'`.
* `hsmallU` — [SOURCE+OURS] the coarse smallness class, tightened by the counted factor of §3b.
* `hsmallFine` — [OURS] the new line; it is what buys a curved fine background.
* `hS`, `hD2` — [SOURCE] p.427's quadratic `D̃⁽²⁾` and the source operator's existence.
* `hU`, `hδ` — [OURS+SOURCE] the link-deviation class and the threshold in exact rationals.
* **no `hform`, no `hraw`** — both are theorems at this datum (`feedDatumGen_isPrintedG1Form`,
  `feedDatumGen_hraw_on_range`).  `hraw` is discharged only ON THE MINIMISER RANGE, which §2 proves
  is all the terminal theorem's proof consumes. -/
theorem terminal_at_composed_carriers_generalFine {ell ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallU : frobSupBond U ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFine : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell Ufine ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3))
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (1370001600 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hell : 0 < ell₀ := by omega
  have hthr : frobSupBond U ≤ 1 / (186 * (ell₀ : ℝ) ^ 3) :=
    le_trans hsmallU (le_of_lt (thirteen336_strictly_smaller hell))
  have hκ0 : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond U
      + ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
        * rawErrorCoeff ell Ufine := by
    have h1 : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond U :=
      mul_nonneg (by positivity) (frobSupBond_nonneg U)
    have h2 : (0 : ℝ) ≤ ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
        * rawErrorCoeff ell Ufine :=
      mul_nonneg (norm_nonneg _) (rawErrorCoeff_nonneg ell Ufine)
    linarith
  have hhalf : 4 * Real.sqrt 2 * frobSupBond U
      + ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
        * rawErrorCoeff ell Ufine
      ≤ Real.sqrt (gammaBrick ell₀) / 2 :=
    halfDrift_split hell _ _ (frobSupBond_nonneg U) hsmallU hsmallFine
  exact terminal_wired_posDef_on_range hell2 hstrict hdvd0 U hthr
    (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc (curlCovariantCLM_L2 Ufine)
    (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L)
    (rawSigmaZero ell) _ (rawSigmaZero_pos (ell_pos_of_scale h)) hκ0 hhalf
    (fun B => feedDatumGen_isPrintedG1Form h Ufine heps (le_of_lt bc.a_pos) _)
    (feedDatumGen_hraw_on_range h Ufine heps (le_of_lt bc.a_pos) U)
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

/-! ## §5 — WHAT THE NEW LINE COSTS, AND THE NON-DEGENERACY ROWS -/

/-- **§5a — AT A FLAT FINE BACKGROUND THE NEW HYPOTHESIS IS FREE.**  `rawErrorCoeff ℓ 1 = 0`
(`HrawCarriers.rawErrorCoeff_trivialU`, CITED), so `hsmallFine` holds for EVERY datum and every
`ℓ₀ ≥ 1`.  So §4 contains `HrawFeed.terminal_at_composed_carriers`'s regime, at a coarse smallness
tighter by the counted factor `2`, and the general-fine content of §4 must NOT be read off any flat
instance (S82). -/
theorem hsmallFine_free_at_flat_fine {ell ell₀ : ℕ} (hell : 0 < ell₀) (K : ℝ) :
    K * rawErrorCoeff (L := L) ell (trivialU L) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  rw [rawErrorCoeff_trivialU ell, mul_zero]
  positivity

/-- **§5b — THE NEW HYPOTHESIS IS NOT VACUOUSLY UNSATISFIABLE AT A CURVED FINE BACKGROUND EITHER:
it is a bound on ONE product, and `rawErrorCoeff ℓ U_fine = (36√2/√ℓ)·α₁(U_fine)` is CONTINUOUSLY
scaled by `α₁(U_fine)`.**  Stated as the exact arithmetic a curved-fine witness must satisfy, so no
reader has to reconstruct it: it suffices that `α₁(U_fine) ≤ √ℓ/(2356·36√2·K·ℓ₀³)` for any `K`
bounding `‖H₁‖`. `§5c` supplies such a `K` in named factors. -/
theorem hsmallFine_of_alphaFine_small {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (K : ℝ) (hK : 0 ≤ K)
    (hα : frobSupBond Ufine
      ≤ Real.sqrt (ell : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * (ell₀ : ℝ) ^ 3)) :
    K * rawErrorCoeff ell Ufine ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell₀
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  have hle : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr hle
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hKp : (0 : ℝ) < K + 1 := by linarith
  have hα0 := frobSupBond_nonneg Ufine
  have hdenpos : (0 : ℝ) < 2356 * (36 * Real.sqrt 2) * (K + 1) * (ell₀ : ℝ) ^ 3 := by positivity
  -- `rawErrorCoeff = (36√2/√ell)·α₁`
  have hre : rawErrorCoeff ell Ufine = (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine :=
    rfl
  rw [hre]
  have hchain : K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine)
      ≤ (K + 1) * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ))
        * (Real.sqrt (ell : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * (ell₀ : ℝ) ^ 3))) := by
    have hcoef : (0 : ℝ) ≤ 36 * Real.sqrt 2 / Real.sqrt (ell : ℝ) := by positivity
    have hmul : (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine
        ≤ (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ))
          * (Real.sqrt (ell : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * (ell₀ : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left hα hcoef
    have hnn : (0 : ℝ) ≤ (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine :=
      mul_nonneg hcoef hα0
    nlinarith [hmul, hnn, hK]
  refine le_trans hchain (le_of_eq ?_)
  field_simp

/-! ### §5c — `‖H₁‖` AT THE GENERAL-FINE DATUM, IN NAMED FACTORS

`§5b` needs a `K` with `‖H₁‖ ≤ K`.  `TerminalAssembly.norm_solutionOperator_le_of_lift` (REUSED)
supplies one from a coercivity modulus and a lift; both are explicit here, because the `ε·I` summand
of `feedGinvGen` IS a coercivity modulus (`Cm = 1/ε`) and `composedQ` is surjective (§3a), so a
continuous right inverse exists. -/

/-- `‖A‖² ≤ (1/ε)·⟨A, G₁⁻¹A⟩` at the general-fine datum: the `ε·I` summand alone, the other two being
squared norms with nonnegative coefficients. -/
theorem feedGinvGen_coercive {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (A : BondFnL2 L) :
    ‖A‖ ^ 2 ≤ (1 / eps) * (inner ℝ A ((feedDatumGen h Ufine heps ha).Ginv A) : ℝ) := by
  rw [feedDatumGen_Ginv h Ufine heps ha, inner_feedGinvGen]
  have h1 : (0 : ℝ) ≤ ‖curlCovariantCLM_L2 Ufine A‖ ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ a * ‖composedQ h Ufine A‖ ^ 2 := mul_nonneg ha (sq_nonneg _)
  have hz : (1 / eps) * (‖curlCovariantCLM_L2 Ufine A‖ ^ 2 + eps * ‖A‖ ^ 2
      + a * ‖composedQ h Ufine A‖ ^ 2)
      = (‖curlCovariantCLM_L2 Ufine A‖ ^ 2 + eps * ‖A‖ ^ 2
        + a * ‖composedQ h Ufine A‖ ^ 2) / eps := by ring
  rw [hz, le_div_iff₀ heps]
  linarith [h1, h2]

/-- **A CONTINUOUS RIGHT INVERSE OF `composedQ` EXISTS AT EVERY FINE BACKGROUND.**  From §3a's
surjectivity and finite dimension; the point is that §5c's `K` is then a real number and not a
promise. -/
theorem exists_continuous_rightInverse {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ∃ Rq : BondFnL2 L' →L[ℝ] BondFnL2 L, ∀ B : BondFnL2 L', composedQ h Ufine (Rq B) = B := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    ((composedQ h Ufine) : BondFnL2 L →ₗ[ℝ] BondFnL2 L')
    (LinearMap.range_eq_top.mpr (composedQ_surjective_gen h Ufine))
  refine ⟨LinearMap.toContinuousLinearMap g, fun B => ?_⟩
  have hB := LinearMap.congr_fun hg B
  simpa using hB

/-- **`‖H₁‖ ≤ √((1/ε)·(‖∂_{U_fine}∘R‖² + ε‖R‖² + a))` FOR ANY RIGHT INVERSE `R` OF `Q`.**  Every
factor on the right is an operator norm or a chosen constant; nothing is left abstract.  Composed
from `TerminalAssembly.norm_solutionOperator_le_of_lift` (REUSED) with the coercivity modulus of
`feedGinvGen_coercive`. -/
theorem norm_H1_feedDatumGen_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a)
    (Rq : BondFnL2 L' →L[ℝ] BondFnL2 L) (hRq : ∀ B : BondFnL2 L', composedQ h Ufine (Rq B) = B) :
    ‖solutionOperator (feedDatumGen h Ufine heps ha)‖
      ≤ Real.sqrt ((1 / eps)
          * (‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 + eps * ‖Rq‖ ^ 2 + a)) := by
  refine norm_solutionOperator_le_of_lift (feedDatumGen h Ufine heps ha) (1 / eps) _
    (by positivity) (by positivity) (feedGinvGen_coercive h Ufine heps ha) Rq
    (fun B => hRq B) (fun B => ?_)
  rw [feedDatumGen_Ginv h Ufine heps ha, inner_feedGinvGen, hRq B]
  have hd : ‖curlCovariantCLM_L2 Ufine (Rq B)‖ ≤ ‖(curlCovariantCLM_L2 Ufine).comp Rq‖ * ‖B‖ :=
    ((curlCovariantCLM_L2 Ufine).comp Rq).le_opNorm B
  have hr : ‖Rq B‖ ≤ ‖Rq‖ * ‖B‖ := Rq.le_opNorm B
  have hdn : (0 : ℝ) ≤ ‖curlCovariantCLM_L2 Ufine (Rq B)‖ := norm_nonneg _
  have hrn : (0 : ℝ) ≤ ‖Rq B‖ := norm_nonneg _
  have hdo : (0 : ℝ) ≤ ‖(curlCovariantCLM_L2 Ufine).comp Rq‖ * ‖B‖ := by positivity
  have hro : (0 : ℝ) ≤ ‖Rq‖ * ‖B‖ := by positivity
  have hsq1 : ‖curlCovariantCLM_L2 Ufine (Rq B)‖ ^ 2
      ≤ ‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 * ‖B‖ ^ 2 := by
    nlinarith [hd, hdn, hdo]
  have hsq2 : ‖Rq B‖ ^ 2 ≤ ‖Rq‖ ^ 2 * ‖B‖ ^ 2 := by nlinarith [hr, hrn, hro]
  have hsq3 : eps * ‖Rq B‖ ^ 2 ≤ eps * (‖Rq‖ ^ 2 * ‖B‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hsq2 (le_of_lt heps)
  nlinarith [hsq1, hsq3]

/-- **`‖H₁‖ ≤ √(‖R‖² + 1)` ONCE `ε` IS CHOSEN LARGE ENOUGH.**  Taking `ε ≥ ‖∂_{U_fine}∘R‖² + a`
makes the previous bound's fraction collapse: `(‖∂∘R‖² + ε‖R‖² + a)/ε ≤ ‖R‖² + 1`.

This is the reduction §5b needs.  The `K` bounding `‖H₁‖` in the general-fine smallness line is
therefore controlled by **one operator norm, `‖R‖`, of any right inverse of `Q`** — and by nothing
else about `U_fine`.  `ε` is a parameter of the datum, freely choosable, so this costs nothing. -/
theorem norm_H1_le_of_rightInverse_bound {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a)
    (Rq : BondFnL2 L' →L[ℝ] BondFnL2 L) (hRq : ∀ B : BondFnL2 L', composedQ h Ufine (Rq B) = B)
    (hbig : ‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 + a ≤ eps) :
    ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ ≤ Real.sqrt (‖Rq‖ ^ 2 + 1) := by
  refine le_trans (norm_H1_feedDatumGen_le h Ufine heps ha Rq hRq) (Real.sqrt_le_sqrt ?_)
  have hc : (0 : ℝ) ≤ ‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 := sq_nonneg _
  have hz : (1 / eps) * (‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 + eps * ‖Rq‖ ^ 2 + a)
      = (‖(curlCovariantCLM_L2 Ufine).comp Rq‖ ^ 2 + eps * ‖Rq‖ ^ 2 + a) / eps := by ring
  rw [hz, div_le_iff₀ heps]
  nlinarith [hbig, hc, sq_nonneg ‖Rq‖, heps]

/-- **§5e — THE FLAT-FINE INSTANCE OF §4, EVERY NEW BINDER DISCHARGED.**  `hsmallFine` is free at
`U_fine = 1` (§5a), so §4 specialises with NO extra hypothesis beyond the (counted, factor-`2`
tighter) coarse smallness.  This is the row that shows §4 contains
`HrawFeed.terminal_at_composed_carriers`'s regime rather than replacing it. -/
theorem terminal_generalFine_at_flat_fine {ell ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallU : frobSupBond U ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h (trivialU L) heps (le_of_lt bc.a_pos)) Qext
      (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h (trivialU L) heps (le_of_lt bc.a_pos))‖)
    (hT : 0 < ‖T‖) (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (1370001600 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h (trivialU L) heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h (trivialU L) heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U))
      U ell₀ (dinvC U ell₀) w := by
  have hell : 0 < ell₀ := by omega
  exact terminal_at_composed_carriers_generalFine h (trivialU L) hell2 hstrict hdvd0 U hsmallU bc
    heps (hsmallFine_free_at_flat_fine (ell := ell) hell _) Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT
    hcard hδ w hw

/-! ### §5d — THE DATUM IS NOT COLLAPSED, AND THE WEAKENING IS STRICT **HERE**

Two rows that stop §4 being read as a `Q = I` statement in disguise, and that instantiate §1a's
abstract strictness at the very carriers §4 uses. -/

/-- **THE FIBRE IS POSITIVE-DIMENSIONAL.**  `composedQ` is not injective at `ℓ ≥ 2`
(`HrawCarriers.composedQ_not_injective`, CITED), so — unlike `TerminalAssembly.assemblyDatum`'s
`Q = I` — the minimisation defining `Φ_a` is over a genuine affine fibre. -/
theorem feedDatumGen_Q_not_injective {ell : ℕ} (h : ScaleQuotient L ell L') (hell2 : 2 ≤ ell)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    ¬ Function.Injective (feedDatumGen h Ufine heps ha).Q := by
  rw [feedDatumGen_Q h Ufine heps ha]
  exact composedQ_not_injective h hell2 Ufine

/-- A non-injective continuous linear map has a non-zero kernel vector. -/
theorem exists_kernel_vector {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →L[ℝ] F)
    (hni : ¬ Function.Injective f) : ∃ x : E, x ≠ 0 ∧ f x = 0 := by
  by_contra hc
  push_neg at hc
  refine hni (fun u v huv => ?_)
  by_contra hne
  exact hc (u - v) (sub_ne_zero.mpr hne) (by rw [map_sub, huv, sub_self])

/-- **THE WEAKENING IS STRICT AT THE CARRIERS OF §4.**  At `ℓ ≥ 2` the minimiser range of the
general-fine datum is a PROPER subset of the fine carrier, so `OnMinimizerRange` is a strictly weaker
hypothesis there than the universal binder — §1a's abstract row, instantiated. -/
theorem onMinimizerRange_strictly_weaker_at_feedDatumGen {ell : ℕ} (h : ScaleQuotient L ell L')
    (hell2 : 2 ≤ ell) (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    ∃ P : BondFnL2 L → Prop,
      OnMinimizerRange (feedDatumGen h Ufine heps ha) P ∧ ¬ (∀ A : BondFnL2 L, P A) := by
  obtain ⟨A₀, hA₀, hQ0⟩ := exists_kernel_vector (feedDatumGen h Ufine heps ha).Q
    (feedDatumGen_Q_not_injective h hell2 Ufine heps ha)
  exact onMinimizerRange_strictly_weaker (feedDatumGen h Ufine heps ha) A₀
    (fun B => minimizer_range_misses_kernel _ A₀ hA₀ hQ0 B)

/-- **AND THE SUFFICIENT CONDITION THE UNIVERSAL ROUTE WOULD NEED IS UNSATISFIABLE.**
`HrawCarriers.hraw_composed_of_lower_bound` converts the three-term general-fine bound into the
consumer's two-term shape UNIVERSALLY, under `∀A, ‖A‖ ≤ ρ‖QA‖`.  That hypothesis is false for EVERY
`ρ` at `ℓ ≥ 2`, because `Q` has a non-zero kernel vector.  On the minimiser range the same condition
HOLDS, with `ρ = ‖H₁‖` (next row) — which is precisely why the weakening is the move that works. -/
theorem no_global_lower_bound_composedQ {ell : ℕ} (h : ScaleQuotient L ell L') (hell2 : 2 ≤ ell)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ρ : ℝ) :
    ¬ (∀ A : BondFnL2 L, ‖A‖ ≤ ρ * ‖composedQ h Ufine A‖) := by
  intro hall
  obtain ⟨A₀, hA₀, hQ0⟩ := exists_kernel_vector (composedQ h Ufine)
    (composedQ_not_injective h hell2 Ufine)
  have hb := hall A₀
  rw [hQ0, norm_zero, mul_zero] at hb
  exact hA₀ (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- **THE SAME CONDITION, ON THE MINIMISER RANGE, WITH `ρ = ‖H₁‖`.**  From `interpolates` alone. -/
theorem range_lower_bound_at_H1 {Ks₀ : Type*} [NormedAddCommGroup Ks₀] [InnerProductSpace ℝ Ks₀]
    {Hs₀ : Type*} [NormedAddCommGroup Hs₀] [InnerProductSpace ℝ Hs₀]
    (D : BalabanCovarianceData Hs₀ Ks₀) (B : Ks₀) :
    ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖D.Q (solutionOperator D B)‖ := by
  rw [interpolates D B]
  exact (solutionOperator D).le_opNorm B

#print axioms composedQ_surjective_gen
#print axioms feedGinvGen
#print axioms inner_feedGinvGen
#print axioms feedGinvGen_selfAdjoint
#print axioms feedGinvGen_posDef
#print axioms feedDatumGen
#print axioms feedDatumGen_Q
#print axioms feedDatumGen_Ginv
#print axioms feedDatumGen_isPrintedG1Form
#print axioms feedDatumGen_hraw_on_range
#print axioms halfDrift_split
#print axioms thirteen336_strictly_smaller
#print axioms terminal_at_composed_carriers_generalFine
#print axioms hsmallFine_free_at_flat_fine
#print axioms hsmallFine_of_alphaFine_small
#print axioms feedGinvGen_coercive
#print axioms exists_continuous_rightInverse
#print axioms norm_H1_feedDatumGen_le
#print axioms norm_H1_le_of_rightInverse_bound
#print axioms terminal_generalFine_at_flat_fine
#print axioms feedDatumGen_Q_not_injective
#print axioms exists_kernel_vector
#print axioms onMinimizerRange_strictly_weaker_at_feedDatumGen
#print axioms no_global_lower_bound_composedQ
#print axioms range_lower_bound_at_H1

end AdalyFormal.TerminalBinder
