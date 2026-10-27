/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import SchurComposed
import SourceWiredComposed
import CovDataCtor
import AdalyFormal.Balaban.DeltaKFull

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `TerminalAssembly.lean` — DISCHARGING THE SCHUR FLOOR'S CARRIED INPUTS

`compute/schur_floor/stage/SchurComposed.lean`'s `schur_floor_on_printed_carrier` carries THREE
inputs: `hs` (CMP99b (3.128)'s split), `hKcurl` (curl domination of `Kop`), `hcontract` (the energy
contraction).  This module discharges the first two OUTRIGHT, replaces the third by a hypothesis
shape that is a THEOREM in the tree at general `U`, and composes the result with the source term.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  interpolates isMinimal)
open AdalyFormal.Balaban.Gamma1Positive (IsAQuadSplit deltaKQuadForm deltaKQuadForm_eq
  inner_solutionOperator_Ginv)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {Hs Ks P₁ P₂ P₃ : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]
  [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
  [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]
  [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]

/-! ## §1 — `hs` DISCHARGED CANONICALLY, AND WHY THAT ALONE IS WORTH NOTHING

`IsAQuadSplit D a Kop` says `⟨A,G₁⁻¹A⟩ = ⟨A,KopA⟩ + a‖QA‖²`.  Taking `Kop` to be the `a`-free
DIFFERENCE makes it hold by construction, for every datum and every `a`.  This is the same move
`compute/g5_g7_thread/stage/G5MassThread.lean`'s `isG1Decomp_canonical` makes for `IsG1Decomp`, and
the same warning applies verbatim: **the predicate alone carries no content; it is a NAMING.**  What
the canonical choice buys is that `hKcurl` — the OTHER carried input — becomes a statement about
`G₁⁻¹` itself, with no free operator left in it.  §2 is where content enters. -/

/-- **`Kop := G₁⁻¹ − a·Q*Q`**, the `a`-free part of `G₁⁻¹` as a continuous linear map. -/
noncomputable def canonicalKop (D : BalabanCovarianceData Hs Ks) (a : ℝ) : Hs →L[ℝ] Hs :=
  D.Ginv - a • (D.Qstar.comp D.Q)

/-- `⟨A, Q*QA⟩ = ‖QA‖²`, from the structure's own adjoint field.  `Qstar` is a CARRIED operator,
never `.adjoint`, so this is the only route to the identity and it uses no topology. -/
theorem inner_Qstar_Q (D : BalabanCovarianceData Hs Ks) (A : Hs) :
    (inner ℝ A (D.Qstar (D.Q A)) : ℝ) = ‖D.Q A‖ ^ 2 := by
  rw [← D.Q_Qstar_adjoint A (D.Q A), real_inner_self_eq_norm_sq]

/-- The canonical `Kop`'s quadratic form, expanded. -/
theorem inner_canonicalKop (D : BalabanCovarianceData Hs Ks) (a : ℝ) (A : Hs) :
    (inner ℝ A (canonicalKop D a A) : ℝ)
      = (inner ℝ A (D.Ginv A) : ℝ) - a * ‖D.Q A‖ ^ 2 := by
  show (inner ℝ A ((D.Ginv - a • (D.Qstar.comp D.Q)) A) : ℝ) = _
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.smul_apply,
    real_inner_smul_right]
  show (inner ℝ A (D.Ginv A) : ℝ) - a * (inner ℝ A (D.Qstar (D.Q A)) : ℝ) = _
  rw [inner_Qstar_Q]

/-- **`hs` IS A THEOREM AT THE CANONICAL `Kop`, FOR EVERY DATUM AND EVERY `a`.**  So the first of
`SchurComposed`'s three carried inputs is discharged — and, exactly as `G5MassThread` §1c says of
its analogue, the discharge is a NAMING, not a fact about Bałaban's operator. -/
theorem canonical_isAQuadSplit (D : BalabanCovarianceData Hs Ks) (a : ℝ) :
    IsAQuadSplit D a (canonicalKop D a) := by
  intro A
  rw [inner_canonicalKop]
  ring

/-- **THE CANONICAL SPLIT IS THE UNIQUE ONE, AT THE LEVEL OF FORMS.**  Any `Kop` satisfying
`IsAQuadSplit D a Kop` has the SAME quadratic form as `canonicalKop D a`.  So §2's hypothesis on the
canonical `Kop` is not a hypothesis about a lucky choice: it is equivalent to the same hypothesis on
every admissible `Kop`, which is why discharging `hs` canonically costs nothing downstream. -/
theorem isAQuadSplit_form_unique (D : BalabanCovarianceData Hs Ks) (a : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D a Kop) (A : Hs) :
    (inner ℝ A (Kop A) : ℝ) = (inner ℝ A (canonicalKop D a A) : ℝ) := by
  have h := hs A
  rw [inner_canonicalKop]
  linarith

/-! ## §2 — CMP99b (3.128) AS A NAMED FORM, AND `hKcurl` DISCHARGED FROM IT

CMP99b p.421 (3.128), as `compute/sol_deltak_readjudicate/SOL_VERDICT.md` Q1 adjudicates it and
`G5MassThread.IsG1Decomp` carries it:

    ⟨A, G₁⁻¹A⟩  =  ⟨A, Δ_π A⟩  −  2⟨HC_π⁽²⁾(A), J⟩  +  ‖RD*A‖²  +  a‖QA‖² .

`IsPrintedG1Form` below is that equation with the FIRST summand named as a squared norm `‖dA‖²`
(the covariant curl energy — `Δ_π` is a Gram operator `d*d`, so its form IS a squared norm) and the
`‖RD*A‖²` summand named `‖pen A‖²`.  **The source term `−2⟨HC⁽²⁾,J⟩` is NOT in this predicate**: the
source is carried separately, in `deltak_wiring`'s `printedDeltaKOp`, and §6 composes the two.  So
`IsPrintedG1Form` is (3.128) for the `J`-FREE covariance, which is exactly the operator whose floor
is `γ₁` (`SourceWiredThreshold`'s own reading of the `γ₁` slot).

**Source status.**  `D.Ginv` is an interface field; no Lean statement can assert that it IS
Bałaban's `G₁⁻¹`.  `IsPrintedG1Form` is the named carrier of an image-verified upstream reading, not
a claim proved here.  Its two structural consequences (§2a, §2b) ARE proved here. -/

/-- **CMP99b (3.128), `J`-free part, as a named hypothesis.**  `d` is the covariant coboundary
(`⟨A,Δ_πA⟩ = ‖dA‖²`), `pen` the divergence penalty (`‖RD*A‖²`), `a` the averaging constant. -/
def IsPrintedG1Form (D : BalabanCovarianceData Hs Ks) (a : ℝ) (d : Hs →L[ℝ] P₁)
    (pen : Hs →L[ℝ] P₃) : Prop :=
  ∀ A : Hs, (inner ℝ A (D.Ginv A) : ℝ) = ‖d A‖ ^ 2 + ‖pen A‖ ^ 2 + a * ‖D.Q A‖ ^ 2

/-- **§2a — `hKcurl` IS A THEOREM GIVEN (3.128).**  `⟨A, KopA⟩ = ‖dA‖² + ‖penA‖² ≥ ‖dA‖²`.  The
slack is exactly the divergence penalty, and it is nonnegative because it is a squared norm — the
one place where the SHAPE of (3.128) (a sum of squares, not an arbitrary sum) is load-bearing.

This discharges the second of `SchurComposed`'s three carried inputs. -/
theorem hKcurl_of_printedG1Form {D : BalabanCovarianceData Hs Ks} {a : ℝ} {d : Hs →L[ℝ] P₁}
    {pen : Hs →L[ℝ] P₃} (hform : IsPrintedG1Form D a d pen) (A : Hs) :
    ‖d A‖ ^ 2 ≤ (inner ℝ A (canonicalKop D a A) : ℝ) := by
  rw [inner_canonicalKop, hform A]
  nlinarith [sq_nonneg ‖pen A‖, norm_nonneg (pen A)]

/-- **§2b — THE EXCESS IS EXACTLY THE PENALTY.**  Stated as an equality so the size of the slack in
§2a is visible and cannot be mistaken for a lost constant. -/
theorem canonicalKop_excess {D : BalabanCovarianceData Hs Ks} {a : ℝ} {d : Hs →L[ℝ] P₁}
    {pen : Hs →L[ℝ] P₃} (hform : IsPrintedG1Form D a d pen) (A : Hs) :
    (inner ℝ A (canonicalKop D a A) : ℝ) - ‖d A‖ ^ 2 = ‖pen A‖ ^ 2 := by
  rw [inner_canonicalKop, hform A]
  ring

/-- **BOTH CARRIED INPUTS AT ONCE**, in the exact shape `SchurComposed` consumes them. -/
theorem printedG1Form_discharges_two {D : BalabanCovarianceData Hs Ks} {a : ℝ} {d : Hs →L[ℝ] P₁}
    {pen : Hs →L[ℝ] P₃} (hform : IsPrintedG1Form D a d pen) :
    IsAQuadSplit D a (canonicalKop D a)
    ∧ ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (canonicalKop D a A) : ℝ) :=
  ⟨canonical_isAQuadSplit D a, fun A => hKcurl_of_printedG1Form hform A⟩

/-! ### §2c — CONTROLS: THE SHAPE OF (3.128) IS LOAD-BEARING

Three refutation rows.  Each names the mutation of `IsPrintedG1Form` it kills, so a reader can see
that §2a is not true of every three-summand decomposition. -/

/-- **MUST-NOT-FIRE — a SIGNED penalty breaks §2a.**  With the `+‖penA‖²` summand replaced by a
general real `c A` of unrestricted sign, `hKcurl` FAILS.  Named refutation on `ℝ`: `Ginv = 0`,
`Q = 0`, `d = id`, `c A = −A²`, `a = 0`; the "form" identity holds and `‖dA‖² ≤ ⟨A,KopA⟩` is false
at `A = 1`.  `nlinarith` is not asked to guess: both sides are computed. -/
theorem signed_penalty_breaks_hKcurl :
    (∀ A : ℝ, (inner ℝ A ((0 : ℝ →L[ℝ] ℝ) A) : ℝ)
        = ‖(ContinuousLinearMap.id ℝ ℝ) A‖ ^ 2 + (-(A ^ 2)) + 0 * ‖(0 : ℝ →L[ℝ] ℝ) A‖ ^ 2)
    ∧ ¬ (‖(ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)‖ ^ 2
        ≤ (inner ℝ (1 : ℝ) ((0 : ℝ →L[ℝ] ℝ) (1 : ℝ)) : ℝ)) := by
  constructor
  · intro A
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, inner_zero_right,
      Real.norm_eq_abs, sq_abs, abs_zero]
    ring
  · intro h
    have h1 : ‖(ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)‖ ^ 2 = 1 := by
      show ‖(1 : ℝ)‖ ^ 2 = 1
      simp
    have h2 : (inner ℝ (1 : ℝ) ((0 : ℝ →L[ℝ] ℝ) (1 : ℝ)) : ℝ) = 0 := by
      show (inner ℝ (1 : ℝ) (0 : ℝ) : ℝ) = 0
      simp
    rw [h1, h2] at h
    norm_num at h

/-- **MUST-NOT-FIRE — the `a`-slot must be the SAME `a`.**  `canonical_isAQuadSplit` is stated at the
canonical `Kop` FOR THAT `a`.  Using a different constant destroys it: on `ℝ` with `Ginv = id`,
`Q = id`, `IsAQuadSplit D 1 (canonicalKop D 0)` is FALSE at `A = 1` (it would read `1 = 1 + 1`).
This is the row that shows the `a` in `hs` and the `a` (3.156) subtracts cannot drift apart. -/
theorem mismatched_a_breaks_split (D : BalabanCovarianceData Hs Ks) (a b : ℝ) (hab : a ≠ b)
    (A₀ : Hs) (hQ : D.Q A₀ ≠ 0) : ¬ IsAQuadSplit D b (canonicalKop D a) := by
  intro hbad
  have h := hbad A₀
  rw [inner_canonicalKop] at h
  have hpos : 0 < ‖D.Q A₀‖ ^ 2 := by
    have : 0 < ‖D.Q A₀‖ := norm_pos_iff.mpr hQ
    positivity
  have : a = b := by
    have hz : (b - a) * ‖D.Q A₀‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with h1 | h2
    · linarith
    · exact absurd h2 (ne_of_gt hpos)
  exact hab this

/-- **S82 GARBAGE SUBSTITUTION — `hKcurl_of_printedG1Form` is NOT algebraically forced.**  Replace
the object under test (`Kop`) by a structurally invalid one — the ZERO operator, which satisfies no
split — and the conclusion `‖dA‖² ≤ ⟨A,0A⟩` is FALSE whenever `dA ≠ 0`.  So the theorem is consuming
`hform`, not deriving its conclusion from nothing. -/
theorem hKcurl_not_forced (d : Hs →L[ℝ] P₁) (A₀ : Hs) (hd : d A₀ ≠ 0) :
    ¬ (‖d A₀‖ ^ 2 ≤ (inner ℝ A₀ ((0 : Hs →L[ℝ] Hs) A₀) : ℝ)) := by
  intro h
  have hz : (inner ℝ A₀ ((0 : Hs →L[ℝ] Hs) A₀) : ℝ) = 0 := by
    show (inner ℝ A₀ (0 : Hs) : ℝ) = 0
    simp
  rw [hz] at h
  have : 0 < ‖d A₀‖ ^ 2 := by
    have : 0 < ‖d A₀‖ := norm_pos_iff.mpr hd
    positivity
  linarith

/-! ## §3 — THE THIRD INPUT: `hcontract`'s SHAPE IS THE WRONG ONE AT GENERAL `U`

`SchurComposed`'s `hcontract` is `∀A, E(QA) ≤ σ²‖dA‖²` — a PURE contraction, with no additive term.
§3a proves that shape is FALSIFIABLE by a single vector, and §3b gives the shape the tree actually
proves at general `U`, together with the absorption that turns it into a floor.

**The tree's own evidence, cited not rebuilt.**  At `U = 1`, between the one pair of levels the tree
can express, the pure shape is a THEOREM with `σ² = 1/ℓ`
(`compute/schur_floor/stage/CoarseCurlContraction.lean`, `coarse_curl_energy_contraction`).  At
general `U` what the tree proves is NOT of that shape: `compute/mech_edges/stage/MechG16.lean`'s
`hraw_op` delivers

    ‖d₁(Q_U A)‖  ≤  ℓ^{-1/2}·‖d_U A‖  +  36√2·ℓ^{-1/2}·α₁·‖A‖ ,

with an additive `‖A‖` term whose coefficient vanishes exactly at `α₁ = 0`.  §3a explains why that
additive term cannot be dropped: the drift is not controlled by `‖d_U A‖`. -/

/-- **§3a — THE PURE CONTRACTION SHAPE IS REFUTED BY ONE VECTOR.**  If some `A₀` has `d A₀ = 0` while
`E(Q A₀) > 0`, then `∀A, E(QA) ≤ σ²‖dA‖²` is FALSE for EVERY `σ²` — no smallness, no positivity, no
choice of constant repairs it.

This is why `hcontract` cannot be obtained from `hraw_op` by algebra: `hraw_op`'s right-hand side is
`σ₀‖dA‖ + c‖A‖`, and at such an `A₀` it is `c‖A₀‖ > 0` while `hcontract` demands `0`.  The two
hypotheses are not related by weakening in either direction at general `U`. -/
theorem pure_contraction_refuted_by_flat_kernel (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (E : Ks → ℝ)
    (A₀ : Hs) (hd : d A₀ = 0) (hE : 0 < E (Q A₀)) (sigsq : ℝ) :
    ¬ (∀ A : Hs, E (Q A) ≤ sigsq * ‖d A‖ ^ 2) := by
  intro h
  have hb := h A₀
  rw [hd, norm_zero] at hb
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hb
  linarith

/-- **THE SHARP ABSORPTION CONSTANT.**  `((√γP − κ)/σ₀)²`. -/
noncomputable def sharpFloorConst (γP κ σ₀ : ℝ) : ℝ := ((Real.sqrt γP - κ) / σ₀) ^ 2

/-- **§3b — THE FLOOR FROM THE `hraw` SHAPE, SHARP.**

From `‖d₁(QA)‖ ≤ σ₀‖dA‖ + κ‖QA‖`, a pointwise Poincaré `γP‖QA‖² ≤ ‖d₁(QA)‖²`, and curl domination
`‖dA‖² ≤ ⟨A,KopA⟩`:

    ((√γP − κ)/σ₀)² · ‖QA‖²  ≤  ⟨A, Kop A⟩ ,      provided `κ ≤ √γP`.

**LAW-19 — THIS IS NOT A REBUILD, IT IS A SHARPENING.**
`compute/stokes_commu/stage/StokesOneSided.lean`'s `gamma_floor_of_perturbed_chain` proves the same
statement with the constant `(γP − 2κ²)/(2σ₀²)`, obtained by `(x+y)² ≤ 2x² + 2y²`.  §3c proves the
constant here DOMINATES that one always, with slack `(√γP − 2κ)²/(2σ₀²)` — in particular a clean
FACTOR OF TWO at `κ = 0`.  The upstream theorem is not consumed and not edited (LAW-4).

**`hκ : 0 ≤ κ` IS NOT USED BY THIS PROOF AND IS RETAINED DELIBERATELY** (the compiler's unused-binder
linter flags it, and the flag is correct; a nested validator flagged it independently).  The proof
needs only `hκγ : κ ≤ √γP`, which alone makes `(√γP − κ)‖QA‖` nonnegative.  Dropping `hκ` leaves a
statement that is still TRUE, but admits `κ < 0` — a NEGATIVE drift coefficient, which denotes
nothing in the object this hypothesis carries (`κ = 36√2·ℓ^{-1/2}·α₁·‖H₁‖`, manifestly `≥ 0`) and at
which the constant `((√γP − κ)/σ₀)²` grows without bound.  The binder stays to keep the theorem
inside its intended regime.  Same practice, and same reason, as
`TerminalCompose.gammaBrick_le_coefficient`'s `hell`. -/
theorem floor_of_hraw_sharp (Q : Hs →L[ℝ] Ks) (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂)
    (Kop : Hs →L[ℝ] Hs) (σ₀ κ γP : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ)
    (hκγ : κ ≤ Real.sqrt γP) (A : Hs)
    (hpert : ‖d₁ (Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖Q A‖)
    (hpoin : γP * ‖Q A‖ ^ 2 ≤ ‖d₁ (Q A)‖ ^ 2)
    (hK : ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) :
    sharpFloorConst γP κ σ₀ * ‖Q A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ) := by
  have hB : (0 : ℝ) ≤ ‖Q A‖ := norm_nonneg _
  have hX : (0 : ℝ) ≤ ‖d A‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ Real.sqrt γP := Real.sqrt_nonneg _
  -- `√γP‖QA‖ ≤ ‖d₁(QA)‖`
  have hlow : Real.sqrt γP * ‖Q A‖ ≤ ‖d₁ (Q A)‖ := by
    have hsq : (Real.sqrt γP * ‖Q A‖) ^ 2 ≤ ‖d₁ (Q A)‖ ^ 2 := by
      rcases le_or_gt (0 : ℝ) γP with hγ0 | hγ0
      · have hγ : (Real.sqrt γP * ‖Q A‖) ^ 2 = γP * ‖Q A‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hγ0]
        rw [hγ]; exact hpoin
      · have hsqz : Real.sqrt γP = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hγ0)
        rw [hsqz, zero_mul]
        have hz : ((0 : ℝ)) ^ 2 = 0 := by ring
        rw [hz]
        positivity
    nlinarith [hsq, norm_nonneg (d₁ (Q A)), mul_nonneg hs0 hB]
  -- `(√γP − κ)‖QA‖ ≤ σ₀‖dA‖`
  have hgap : (Real.sqrt γP - κ) * ‖Q A‖ ≤ σ₀ * ‖d A‖ := by nlinarith [hlow, hpert]
  have hnn : (0 : ℝ) ≤ (Real.sqrt γP - κ) * ‖Q A‖ := mul_nonneg (by linarith) hB
  have hsq2 : ((Real.sqrt γP - κ) * ‖Q A‖) ^ 2 ≤ (σ₀ * ‖d A‖) ^ 2 := by
    nlinarith [hgap, hnn, mul_nonneg (le_of_lt hσ₀) hX]
  have hfin : sharpFloorConst γP κ σ₀ * ‖Q A‖ ^ 2 ≤ ‖d A‖ ^ 2 := by
    unfold sharpFloorConst
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < σ₀ ^ 2)]
    nlinarith [hsq2]
  linarith [hfin, hK]

/-- **§3c — THE SHARP CONSTANT DOMINATES THE UPSTREAM ONE, ALWAYS.**  The excess is
`(√γP − 2κ)²/(2σ₀²) ≥ 0`, so nothing is lost by using §3b, and at `κ = 0` the gain is exactly a
factor of `2`.  Both facts in one statement so neither can be quoted without the other. -/
theorem sharpFloorConst_ge_crude (γP κ σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hγP : 0 ≤ γP) :
    (γP - 2 * κ ^ 2) / (2 * σ₀ ^ 2) ≤ sharpFloorConst γP κ σ₀
    ∧ sharpFloorConst γP 0 σ₀ = 2 * (γP / (2 * σ₀ ^ 2)) := by
  have hden : (0 : ℝ) < 2 * σ₀ ^ 2 := by positivity
  have hsq : Real.sqrt γP ^ 2 = γP := Real.sq_sqrt hγP
  constructor
  · unfold sharpFloorConst
    rw [div_pow, div_le_div_iff₀ hden (by positivity : (0 : ℝ) < σ₀ ^ 2)]
    nlinarith [sq_nonneg (Real.sqrt γP - 2 * κ), hsq, Real.sqrt_nonneg γP, sq_nonneg σ₀,
      hσ₀, mul_pos hσ₀ hσ₀]
  · unfold sharpFloorConst
    rw [sub_zero, div_pow, hsq]
    field_simp

/-! ## §4 — `‖H₁‖`, DERIVED AT AN ARBITRARY DATUM

`SourceWiredThreshold`'s threshold `2‖H₁‖c₂‖J‖ < γ₁` needs a bound on `‖solutionOperator D‖`.  The
`≤ 1` available in the tree (`SourceWired.bondData_opNorm_H1_le_one`) is proved from `H₁ = I` at the
COLLAPSED witness datum and does not transport.  §4 derives a bound at ANY datum, from the
structure's own fields plus ONE named lift.  Nothing is assumed about `Ginv` beyond its own axioms.

The chain: a PSD Cauchy–Schwarz (§4a) turns the structure's invertibility into an explicit coercivity
modulus for `Ginv` (§4b); minimality against a lift bounds `⟨H₁B, G₁⁻¹H₁B⟩` from above (§4c). -/

/-- **§4a — CAUCHY–SCHWARZ FOR THE FORM OF A PSD SELF-ADJOINT OPERATOR.**  `⟨x,Ty⟩² ≤ ⟨x,Tx⟩⟨y,Ty⟩`.
The discriminant argument, done by hand at two explicit values of the parameter (no spectral theory,
no square roots of operators). -/
theorem psd_form_cauchy_schwarz (T : Hs →L[ℝ] Hs)
    (hsa : ∀ x y : Hs, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (hpsd : ∀ x : Hs, (0 : ℝ) ≤ inner ℝ x (T x)) (x y : Hs) :
    (inner ℝ x (T y) : ℝ) ^ 2 ≤ (inner ℝ x (T x) : ℝ) * (inner ℝ y (T y) : ℝ) := by
  set qxx : ℝ := inner ℝ x (T x) with hqxx
  set qyy : ℝ := inner ℝ y (T y) with hqyy
  set qxy : ℝ := inner ℝ x (T y) with hqxy
  have hsymm : (inner ℝ y (T x) : ℝ) = qxy := by
    rw [hqxy, ← hsa y x, real_inner_comm]
  have hexp : ∀ t : ℝ, (inner ℝ (x + t • y) (T (x + t • y)) : ℝ)
      = qxx + 2 * t * qxy + t ^ 2 * qyy := by
    intro t
    simp only [map_add, ContinuousLinearMap.map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hsymm, ← hqxx, ← hqyy, ← hqxy]
    ring
  have hall : ∀ t : ℝ, 0 ≤ qxx + 2 * t * qxy + t ^ 2 * qyy := by
    intro t
    rw [← hexp t]; exact hpsd _
  rcases eq_or_lt_of_le (hpsd y) with hz | hpos
  · -- `qyy = 0`: the quadratic is affine and nonnegative everywhere, forcing `qxy = 0`
    have hyy : qyy = 0 := by rw [hqyy]; exact hz.symm
    have hxy : qxy = 0 := by
      by_contra hne
      have h1 := hall (-(qxx + 1) / (2 * qxy))
      rw [hyy] at h1
      have h2 : 2 * (-(qxx + 1) / (2 * qxy)) * qxy = -(qxx + 1) := by
        field_simp
      rw [h2] at h1
      linarith
    rw [hxy, hyy]
    simp
  · -- `qyy > 0`: evaluate at the minimiser
    have hyy : 0 < qyy := by rw [hqyy]; exact hpos
    have h1 := hall (-qxy / qyy)
    have h2 : 2 * (-qxy / qyy) * qxy = -2 * qxy ^ 2 / qyy := by field_simp
    have h3 : (-qxy / qyy) ^ 2 * qyy = qxy ^ 2 / qyy := by field_simp
    rw [h2, h3] at h1
    have hcollapse : qxx + -2 * qxy ^ 2 / qyy + qxy ^ 2 / qyy = qxx - qxy ^ 2 / qyy := by ring
    rw [hcollapse] at h1
    have h4 : qxy ^ 2 / qyy ≤ qxx := by linarith
    rw [div_le_iff₀ hyy] at h4
    linarith [h4]

/-- **`‖Tx‖² ≤ ‖T‖·⟨x,Tx⟩`** for PSD self-adjoint `T` — the operator-norm consequence of §4a. -/
theorem normSq_le_opNorm_mul_form (T : Hs →L[ℝ] Hs)
    (hsa : ∀ x y : Hs, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y))
    (hpsd : ∀ x : Hs, (0 : ℝ) ≤ inner ℝ x (T x)) (x : Hs) :
    ‖T x‖ ^ 2 ≤ ‖T‖ * (inner ℝ x (T x) : ℝ) := by
  have hkey : (inner ℝ x (T (T x)) : ℝ) ^ 2
      ≤ (inner ℝ x (T x) : ℝ) * (inner ℝ (T x) (T (T x)) : ℝ) :=
    psd_form_cauchy_schwarz T hsa hpsd x (T x)
  have hxx : (inner ℝ x (T (T x)) : ℝ) = ‖T x‖ ^ 2 := by
    rw [← hsa x (T x), real_inner_comm, real_inner_self_eq_norm_sq]
  have hb : (inner ℝ (T x) (T (T x)) : ℝ) ≤ ‖T‖ * ‖T x‖ ^ 2 := by
    have h1 : (inner ℝ (T x) (T (T x)) : ℝ) ≤ ‖T x‖ * ‖T (T x)‖ :=
      real_inner_le_norm _ _
    have h2 : ‖T (T x)‖ ≤ ‖T‖ * ‖T x‖ := T.le_opNorm (T x)
    nlinarith [h1, h2, norm_nonneg (T x)]
  rw [hxx] at hkey
  rcases eq_or_lt_of_le (norm_nonneg (T x)) with hz | hpos
  · have hz2 : ‖T x‖ ^ 2 = 0 := by rw [← hz]; ring
    rw [hz2]
    exact mul_nonneg (norm_nonneg T) (hpsd x)
  · have hs : 0 < ‖T x‖ ^ 2 := by positivity
    nlinarith [hkey, hb, hs, hpsd x, norm_nonneg T]

/-- **§4b — AN EXPLICIT COERCIVITY MODULUS FOR `G₁⁻¹`, FROM THE STRUCTURE'S OWN FIELDS.**

    ‖A‖²  ≤  ‖G₁‖²·‖G₁⁻¹‖ · ⟨A, G₁⁻¹A⟩       for every `A`.

No hypothesis: `Ginv_selfAdjoint`, `Ginv_posSemidef` and the two-sided inverse `Gstar` are all
structure fields.  Stated in MULTIPLIED form so that no division by a possibly-zero norm occurs and
no junk value can make it vacuously true. -/
theorem ginv_coercive_multiplied (D : BalabanCovarianceData Hs Ks) (A : Hs) :
    ‖A‖ ^ 2 ≤ ‖D.Gstar‖ ^ 2 * ‖D.Ginv‖ * (inner ℝ A (D.Ginv A) : ℝ) := by
  have h1 : ‖A‖ ≤ ‖D.Gstar‖ * ‖D.Ginv A‖ := by
    have hid : D.Gstar (D.Ginv A) = A := D.Gstar_Ginv A
    have := D.Gstar.le_opNorm (D.Ginv A)
    rw [hid] at this
    exact this
  have h1sq : ‖A‖ ^ 2 ≤ ‖D.Gstar‖ ^ 2 * ‖D.Ginv A‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖D.Gstar‖ * ‖D.Ginv A‖ := by positivity
    nlinarith [h1, norm_nonneg A, hnn]
  have h2 : ‖D.Ginv A‖ ^ 2 ≤ ‖D.Ginv‖ * (inner ℝ A (D.Ginv A) : ℝ) :=
    normSq_le_opNorm_mul_form D.Ginv D.Ginv_selfAdjoint D.Ginv_posSemidef A
  have hg : (0 : ℝ) ≤ ‖D.Gstar‖ ^ 2 := by positivity
  nlinarith [h1sq, h2, hg]

/-- **§4c — `‖H₁‖ ≤ √(Cm·M)`.**  `Cm` is any coercivity constant for `G₁⁻¹` in the multiplied form
(§4b supplies `‖G₁‖²‖G₁⁻¹‖`), and `M` bounds the energy of ONE named lift `Rq` of the constraint.
Minimality (`VariationalProjectorH1.isMinimal`, reused) does the work: `H₁B` is the cheapest
interpolation, so any lift bounds it. -/
theorem norm_solutionOperator_le_of_lift (D : BalabanCovarianceData Hs Ks) (Cm M : ℝ)
    (hCm : 0 ≤ Cm) (hM : 0 ≤ M)
    (hcoer : ∀ A : Hs, ‖A‖ ^ 2 ≤ Cm * (inner ℝ A (D.Ginv A) : ℝ))
    (Rq : Ks →L[ℝ] Hs) (hRq : ∀ B : Ks, D.Q (Rq B) = B)
    (hlift : ∀ B : Ks, (inner ℝ (Rq B) (D.Ginv (Rq B)) : ℝ) ≤ M * ‖B‖ ^ 2) :
    ‖solutionOperator D‖ ≤ Real.sqrt (Cm * M) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun B => ?_
  have hmin : (inner ℝ (solutionOperator D B) (D.Ginv (solutionOperator D B)) : ℝ)
      ≤ inner ℝ (Rq B) (D.Ginv (Rq B)) := isMinimal D B (Rq B) (hRq B)
  have hchain : ‖solutionOperator D B‖ ^ 2 ≤ (Cm * M) * ‖B‖ ^ 2 := by
    have h1 := hcoer (solutionOperator D B)
    have h2 := hlift B
    nlinarith [h1, h2, hmin, hCm, sq_nonneg ‖B‖]
  have hsq : Real.sqrt (‖solutionOperator D B‖ ^ 2) ≤ Real.sqrt ((Cm * M) * ‖B‖ ^ 2) :=
    Real.sqrt_le_sqrt hchain
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg B)]
    at hsq
  exact hsq

/-- **§4d — THE LIFT BINDER IS INHABITED**, so §4c is not a statement about an empty hypothesis:
`solutionOperator D` is itself a right inverse of `D.Q` (`interpolates`).  A cheaper lift gives a
better constant; this row only rules out vacuity. -/
theorem lift_binder_inhabited (D : BalabanCovarianceData Hs Ks) :
    ∀ B : Ks, D.Q (solutionOperator D B) = B := interpolates D

/-- **§4e — `‖H₁‖` AT A DATUM SATISFYING (3.128), FULLY IN NAMED FACTORS.**  Composing §4b and §4c
with the printed form: `M = ‖d∘Rq‖² + ‖pen∘Rq‖² + a`, because `Q(RqB) = B` makes the mass summand
exactly `a‖B‖²`. -/
theorem norm_solutionOperator_le_of_printedG1Form (D : BalabanCovarianceData Hs Ks) (a : ℝ)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃) (hform : IsPrintedG1Form D a d pen) (ha : 0 ≤ a)
    (Rq : Ks →L[ℝ] Hs) (hRq : ∀ B : Ks, D.Q (Rq B) = B) :
    ‖solutionOperator D‖
      ≤ Real.sqrt ((‖D.Gstar‖ ^ 2 * ‖D.Ginv‖)
          * (‖d.comp Rq‖ ^ 2 + ‖pen.comp Rq‖ ^ 2 + a)) := by
  refine norm_solutionOperator_le_of_lift D _ _ (by positivity) (by positivity)
    (ginv_coercive_multiplied D) Rq hRq fun B => ?_
  rw [hform (Rq B), hRq B]
  have hd : ‖d (Rq B)‖ ≤ ‖d.comp Rq‖ * ‖B‖ := (d.comp Rq).le_opNorm B
  have hp : ‖pen (Rq B)‖ ≤ ‖pen.comp Rq‖ * ‖B‖ := (pen.comp Rq).le_opNorm B
  have hdn : (0 : ℝ) ≤ ‖d (Rq B)‖ := norm_nonneg _
  have hpn : (0 : ℝ) ≤ ‖pen (Rq B)‖ := norm_nonneg _
  have hdo : (0 : ℝ) ≤ ‖d.comp Rq‖ * ‖B‖ := by positivity
  have hpo : (0 : ℝ) ≤ ‖pen.comp Rq‖ * ‖B‖ := by positivity
  nlinarith [hd, hp, hdn, hpn, hdo, hpo, sq_nonneg ‖B‖]

#print axioms pure_contraction_refuted_by_flat_kernel
#print axioms sharpFloorConst
#print axioms floor_of_hraw_sharp
#print axioms sharpFloorConst_ge_crude
#print axioms psd_form_cauchy_schwarz
#print axioms normSq_le_opNorm_mul_form
#print axioms ginv_coercive_multiplied
#print axioms norm_solutionOperator_le_of_lift
#print axioms lift_binder_inhabited
#print axioms norm_solutionOperator_le_of_printedG1Form

#print axioms canonicalKop
#print axioms inner_Qstar_Q
#print axioms inner_canonicalKop
#print axioms canonical_isAQuadSplit
#print axioms isAQuadSplit_form_unique
#print axioms IsPrintedG1Form
#print axioms hKcurl_of_printedG1Form
#print axioms canonicalKop_excess
#print axioms printedG1Form_discharges_two
#print axioms signed_penalty_breaks_hKcurl
#print axioms mismatched_a_breaks_split
#print axioms hKcurl_not_forced

end AdalyFormal.Balaban.TerminalAssembly

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  interpolates isMinimal)
open AdalyFormal.Balaban.Gamma1Positive (IsAQuadSplit deltaKQuadForm deltaKQuadForm_eq
  deltaKQuadForm_eq_deltaKWiring_form gamma_nonpos_of_kernel Q_ne_zero_of_null)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.CovariantLemma24 (covariant_lemma24)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos gammaBrick_lower
  gammaBrick_le_coefficient cZeroFn cZeroFn_admissible coarseQEnergyCov_cZero_eq_zero
  bondEnergy_eq_normSq curlEnergyCov_eq_inner_dstarDCLM)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (sourceTerm deltaKQuadOp inner_deltaKQuadOp IsSourceOperator
  printedDeltaKOp inner_printedDeltaKOp cdcFormTrue norm_cZero_pos)
open AdalyFormal.Balaban.SourceWired (abs_sourceTerm_le)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {L : PeriodicLatticeExtent}

/-! ## §5 — THE BRICK IN THE `‖C₀B̃‖²` NORM, AND THE CURL IDENTITY

`TerminalCompose.cdc_floor_class_uniform` states the floor with `‖B̃‖²` on the left, obtained from
the `‖C₀B̃‖²` form by `ConstructCDC.norm_le_norm_cZero`.  The source-term threshold
(`SourceWiredThreshold.cdcFormTrue_coercive_of_source_small`) is stated in `‖C₀B̃‖²`, so composing
the two through the `‖B̃‖²` form would need an UPPER bound on `‖C₀‖`, which the tree does not have.

§5a re-derives the `‖C₀B̃‖²` form — the one `covariant_lemma24` actually produces, before the
weakening — so **no bound on `‖C₀‖` is needed anywhere in this lane.**  Nothing new is proved about
Lemma 2.4; the three transports are `TerminalCompose`'s own, reused. -/

/-- **§5a — THE BRICK, UNWEAKENED.**  `((1/360)ℓ⁻⁵ − 96α₁²)·‖C₀B̃‖² ≤ ⟪C₀B̃, D_U^*D_U(C₀B̃)⟫`.
This is `TerminalCompose.cdc_covariant_floor_dstarD` with the final `‖w‖ ≤ ‖C₀w‖` step NOT taken,
and it therefore needs no sign hypothesis on the coefficient (`hcoeff` disappears). -/
theorem cdc_floor_at_cZero_norm {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (w : TildeFn L ell) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2)
        * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  have hmain := covariant_lemma24 (L := L) hell2 hstrict hdvd U (cZeroFn U ell w)
    (cZeroFn_admissible hell hdvd U w)
  rw [coarseQEnergyCov_cZero_eq_zero hell hdvd U w, mul_zero, zero_add] at hmain
  have hfn : cZeroFn U ell w = fun b => (cZero U ell (dinvC U ell) w : BondFnL2 L) b := rfl
  rw [hfn, bondEnergy_eq_normSq, curlEnergyCov_eq_inner_dstarDCLM] at hmain
  exact hmain

/-- **§5b — THE CLASS-UNIFORM CONSTANT, IN THE SAME NORM.** -/
theorem cdc_floor_class_uniform_at_cZero_norm {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (w : TildeFn L ell) :
    gammaBrick ell * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ (inner ℝ (cZero U ell (dinvC U ell) w)
          (dstarDCLM U (cZero U ell (dinvC U ell) w)) : ℝ) := by
  have hell : 0 < ell := by omega
  have hbase := cdc_floor_at_cZero_norm hell2 hstrict hdvd U w
  have hcmp := gammaBrick_le_coefficient hell U hthr
  nlinarith [hbase, hcmp, sq_nonneg ‖cZero U ell (dinvC U ell) w‖]

/-- **§5c — THE CURL COBOUNDARY'S NORM IS THE `D_U^*D_U` FORM.**  `‖∂_U x‖² = ⟪x, D_U^*D_U x⟫` on
`BondFnL2 L`.  Both sides are `DeltaKFull`/`CStarDeltaKCOperator` theorems at `WithLp.toLp` of the
underlying function, and `WithLp.toLp 2 (WithLp.ofLp x) = x` is definitional. -/
theorem normSq_curlCLM_eq_dstarDCLM_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U x‖ ^ 2 = (inner ℝ x (dstarDCLM U x) : ℝ) := by
  have hx : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  have h1 := norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm U (WithLp.ofLp x)
  have h2 := AdalyFormal.Balaban.CStarDeltaKCOperator.inner_dstarDCLM_eq_dstarDQuadForm U
    (WithLp.ofLp x)
  rw [hx] at h1 h2
  rw [h1, h2]

/-- **§5d — THE POINTWISE POINCARÉ INPUT, ASSEMBLED.**  `γP‖B‖² ≤ ‖∂_U B‖²` at `B = C₀B̃`, with
`γP = gammaBrick ell` — the exact shape §3b's `hpoin` consumes. -/
theorem hpoin_at_cZero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    (w : TildeFn L ell) :
    gammaBrick ell * ‖cZero U ell (dinvC U ell) w‖ ^ 2
      ≤ ‖curlCovariantCLM_L2 U (cZero U ell (dinvC U ell) w)‖ ^ 2 := by
  rw [normSq_curlCLM_eq_dstarDCLM_form]
  exact cdc_floor_class_uniform_at_cZero_norm hell2 hstrict hdvd U hthr w

/-! ## §6 — THE SCHUR FLOOR ON THE PRINTED CARRIER, WITH THE `hraw` HYPOTHESIS -/

/-- **THE FLOOR, WITH `hs` AND `hKcurl` DISCHARGED AND `hcontract` REPLACED BY `hraw`.**

For every `ℓ ≥ 2`, every tiled torus, every background `U` in the smallness class, every datum `D`
whose coarse carrier is `BondFnL2 L` and whose `G₁⁻¹` satisfies CMP99b (3.128), and every `B̃`:

    ((√(gammaBrick ℓ) − κ)/σ₀)² · ‖C₀B̃‖²  ≤  ⟨C₀B̃, (Q G₁ Q*)⁻¹ C₀B̃⟩ − a‖C₀B̃‖² .

**Carried inputs: `hform` (3.128) [SOURCE] and `hraw` [OURS].**  `hs` and `hKcurl` are gone — they
are §1 and §2's theorems.  `hraw` is the shape `MechG16.hraw_op` proves at general `U` between the
levels the tree can express (`σ₀ = ℓ^{-1/2}`, `κ = 36√2·ℓ^{-1/2}·α₁·‖H₁‖`); §3a proves the pure
contraction shape `hcontract` is NOT implied by it and is refutable by one vector. -/
theorem schur_floor_hraw_at_cZero {ell : ℕ} (hell2 : 2 ≤ ell)
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
      ≤ deltaKQuadForm D a (cZero U ell (dinvC U ell) w) := by
  set B : BondFnL2 L := cZero U ell (dinvC U ell) w with hB
  set A : Hs := solutionOperator D B with hA
  have hQA : D.Q A = B := interpolates D B
  have hfl := floor_of_hraw_sharp D.Q d (curlCovariantCLM_L2 U) (canonicalKop D a) σ₀ κ
    (gammaBrick ell) hσ₀ hκ hκγ A (hraw A)
    (by rw [hQA]; exact hpoin_at_cZero hell2 hstrict hdvd U hthr w)
    (hKcurl_of_printedG1Form hform A)
  rw [hQA] at hfl
  rw [deltaKQuadForm_eq D a (canonicalKop D a) (canonical_isAQuadSplit D a) B]
  exact hfl

/-! ## §7 — THE SOURCE TERM ON THE PRINTED SUBSPACE ONLY

`SourceWiredThreshold`'s three coercivity theorems all take

    hfloor : ∀ B : BondFnL2 L, γ₁‖B‖² ≤ ⟪B, deltaKQuadOp D bc B⟫

— the floor on the WHOLE coarse carrier.  §7a proves that hypothesis is **UNSATISFIABLE with a
positive `γ₁`** for any covariance whose `a`-free part has a null vector, which is exactly Bałaban's
own situation (`Kop = Δ_π + DRD*` annihilates the constant lattice 1-forms).  So the ambient form
cannot be fed by ANY floor, including this lane's.  §7b restates the threshold using the floor only
at `C₀B̃` — which is all the upstream proof consumes — and that version composes with §6. -/

/-- **§7a — THE FINDING: THE AMBIENT `hfloor` IS UNSATISFIABLE WITH `γ₁ > 0`.**  If some `A₀ ≠ 0`
has `⟨A₀, Kop A₀⟩ ≤ 0` — which under (3.128) means `dA₀ = 0` and `penA₀ = 0` — then every `γ₁`
satisfying the ambient floor is `≤ 0`.  Proved through `Gamma1Reduction.gamma_nonpos_of_kernel` and
`Q_ne_zero_of_null` (both REUSED), with the `deltaKQuadOp`/`deltaKQuadForm` bridge supplied here. -/
theorem ambient_hfloor_forces_gamma_nonpos (D : BalabanCovarianceData Hs (BondFnL2 L))
    (bc : BaseConstant) (γ₁ : ℝ) (Kop : Hs →L[ℝ] Hs)
    (hs : IsAQuadSplit D (usedAt bc 0) Kop) (A₀ : Hs) (hne : A₀ ≠ 0)
    (hK0 : (inner ℝ A₀ (Kop A₀) : ℝ) ≤ 0)
    (hfloor : ∀ B : BondFnL2 L, γ₁ * ‖B‖ ^ 2 ≤ (inner ℝ B (deltaKQuadOp D bc B) : ℝ)) :
    γ₁ ≤ 0 := by
  have hbridge : ∀ B : BondFnL2 L,
      deltaKQuadForm D (usedAt bc 0) B = (inner ℝ B (deltaKQuadOp D bc B) : ℝ) := by
    intro B
    rw [deltaKQuadForm_eq_deltaKWiring_form D bc B, inner_deltaKQuadOp]
  refine gamma_nonpos_of_kernel D (usedAt bc 0) γ₁ Kop hs A₀ hK0
    (Q_ne_zero_of_null D (usedAt bc 0) Kop hs A₀ hne hK0) ?_
  intro B
  rw [hbridge B]
  exact hfloor B

/-- **§7a' — UNDER (3.128) THE NULL VECTOR IS EXACTLY A JOINT KERNEL VECTOR.**  So §7a's hypothesis
is not exotic: any `A₀ ≠ 0` with zero covariant curl and zero divergence penalty triggers it. -/
theorem canonicalKop_null_of_joint_kernel {Ks P₁ P₃ : Type*} [NormedAddCommGroup Ks]
    [InnerProductSpace ℝ Ks] [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    {D : BalabanCovarianceData Hs Ks} {a : ℝ} {d : Hs →L[ℝ] P₁} {pen : Hs →L[ℝ] P₃}
    (hform : IsPrintedG1Form D a d pen) (A₀ : Hs) (hd : d A₀ = 0) (hp : pen A₀ = 0) :
    (inner ℝ A₀ (canonicalKop D a A₀) : ℝ) ≤ 0 := by
  rw [inner_canonicalKop, hform A₀, hd, hp, norm_zero]
  norm_num

/-- **§7b — THE THRESHOLD WITH THE FLOOR AT `C₀B̃` ONLY.**  Character for character
`SourceWiredThreshold.cdcFormTrue_coercive_of_source_small`, with the universally quantified
`hfloor` replaced by its single instance at `B = C₀B̃`.  Nothing else changes — same constant, same
conclusion — because the upstream proof calls `hfloor` exactly once, at that point. -/
theorem cdcFormTrue_coercive_at_cZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell)
    (hfloorAt : γ₁ * ‖cZero U ell Dinv w‖ ^ 2
      ≤ (inner ℝ (cZero U ell Dinv w) (deltaKQuadOp D bc (cZero U ell Dinv w)) : ℝ)) :
    (γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖) * ‖cZero U ell Dinv w‖ ^ 2
      ≤ cdcFormTrue D bc Qext J U ell Dinv w := by
  set B : BondFnL2 L := cZero U ell Dinv w with hB
  have hsplit : cdcFormTrue D bc Qext J U ell Dinv w
      = (inner ℝ B (deltaKQuadOp D bc B) : ℝ) - 2 * sourceTerm D Qext J B := by
    show AdalyFormal.Balaban.DeltaKAssembly.deltaKForm D bc Qext J B = _
    rw [← inner_printedDeltaKOp D bc Qext J S hS B]
    show (inner ℝ B (deltaKQuadOp D bc B - (2 : ℝ) • S B) : ℝ) = _
    rw [inner_sub_right, real_inner_smul_right, hS B]
  have hsrc := abs_sourceTerm_le D Qext J c₂ hc₂ hD2 B
  have hsrc' : sourceTerm D Qext J B ≤ ‖solutionOperator D‖ * c₂ * ‖J‖ * ‖B‖ ^ 2 :=
    le_trans (le_abs_self _) hsrc
  rw [hsplit]
  linarith [hfloorAt, hsrc']

/-- **§7c — POSITIVE DEFINITENESS ON `ℓ²(Λ̃)` FROM THE COMPRESSED FLOOR.** -/
theorem cdcFormTrue_posDef_at_cZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (γ₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0)
    (hfloorAt : γ₁ * ‖cZero U ell Dinv w‖ ^ 2
      ≤ (inner ℝ (cZero U ell Dinv w) (deltaKQuadOp D bc (cZero U ell Dinv w)) : ℝ))
    (hthr : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < γ₁) :
    0 < cdcFormTrue D bc Qext J U ell Dinv w := by
  have hpos : 0 < ‖cZero U ell Dinv w‖ := norm_cZero_pos U Dinv w hw
  have h := cdcFormTrue_coercive_at_cZero D bc Qext J S hS γ₁ c₂ hc₂ hD2 U Dinv w hfloorAt
  have hgap : 0 < γ₁ - 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ := by linarith
  nlinarith [h, mul_pos hgap (pow_pos hpos 2)]

#print axioms cdc_floor_at_cZero_norm
#print axioms cdc_floor_class_uniform_at_cZero_norm
#print axioms normSq_curlCLM_eq_dstarDCLM_form
#print axioms hpoin_at_cZero
#print axioms schur_floor_hraw_at_cZero
#print axioms ambient_hfloor_forces_gamma_nonpos
#print axioms canonicalKop_null_of_joint_kernel
#print axioms cdcFormTrue_coercive_at_cZero
#print axioms cdcFormTrue_posDef_at_cZero

end AdalyFormal.Balaban.TerminalAssembly

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm deltaKQuadForm_eq_deltaKWiring_form)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos gammaBrick_lower)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (deltaKQuadOp inner_deltaKQuadOp IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev norm_source_le_of_linkDev)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {L : PeriodicLatticeExtent}

/-! ## §8 — THE COMPOSED STATEMENT, AND THE THRESHOLD IN EXACT RATIONALS -/

/-- The `deltaKQuadForm`/`deltaKQuadOp` bridge, named. -/
theorem deltaKQuadForm_eq_inner_deltaKQuadOp (D : BalabanCovarianceData Hs (BondFnL2 L))
    (bc : BaseConstant) (B : BondFnL2 L) :
    deltaKQuadForm D (usedAt bc 0) B = (inner ℝ B (deltaKQuadOp D bc B) : ℝ) := by
  rw [deltaKQuadForm_eq_deltaKWiring_form D bc B, inner_deltaKQuadOp]

/-- **THE COMPOSED THEOREM.**  `C*Δ_kC` — the printed three-summand form of CMP99b (3.156),
compressed by `construct_cdc`'s `C₀` onto the printed subspace — is POSITIVE DEFINITE on `ℓ²(Λ̃)`,
for every `ℓ ≥ 2`, every tiled torus, every background `U` in the smallness class
`α₁ ≤ 1/(186ℓ³)`, and every nonzero `B̃`.

**Hypothesis inventory, tagged.**
* `hell2`, `hstrict`, `hdvd` — [OURS] the tiling conditions the corrected `ℓ⁻⁵` Lemma 2.4 needs.
* `hthr` — [SOURCE] the smallness class, `compute/threshold_vs_printed/`'s conversion of (3.35).
* `hform` — [SOURCE] CMP99b (3.128), `J`-free part, image-verified upstream.
* `hraw` — [OURS] the drift-priced chain bound.  `MechG16.hraw_op` proves this SHAPE at general `U`
  between `BondFnL2 L` and `CoarseFnL2 L ell`; at THIS pair of carriers it is carried.
* `hS`, `hD2` — [SOURCE] p.427's "`D̃⁽²⁾(B)` is a quadratic polynomial in `B`", and the existence of
  the source term as an operator (`deltak_wiring`'s co-extensive `IsSourceOperator`).
* `hsmall` — [OURS+SOURCE] the source is below the threshold; §8b/§8c turn it into a bound on the
  link deviation in closed form.

**No `hs`, no `hKcurl`, no `hcontract`.** -/
theorem terminal_printed_posDef {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (hform : IsPrintedG1Form D (usedAt bc 0) d pen)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hκγ : κ ≤ Real.sqrt (gammaBrick ell))
    (hraw : ∀ A : Hs, ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
    (Qext : BondFnL2 L → BondFnL2 L) (J : Hs) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 L, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hsmall : 2 * ‖solutionOperator D‖ * c₂ * ‖J‖ < sharpFloorConst (gammaBrick ell) κ σ₀)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext J U ell (dinvC U ell) w := by
  have hfl := schur_floor_hraw_at_cZero hell2 hstrict hdvd U hthr D (usedAt bc 0) d pen hform
    σ₀ κ hσ₀ hκ hκγ hraw w
  rw [deltaKQuadForm_eq_inner_deltaKQuadOp D bc] at hfl
  exact cdcFormTrue_posDef_at_cZero D bc Qext J S hS _ c₂ hc₂ hD2 U (dinvC U ell) w hw hfl hsmall

/-! ### §8a — THE CONSTANT, BOUNDED BELOW BY AN EXPLICIT RATIONAL

`gammaBrick ℓ ≥ 1/(345960·ℓ⁶)` (`TerminalCompose.gammaBrick_lower`, cited).  Two rows: the clean
`κ = 0` value, and the value under the working hypothesis `κ ≤ ½√(gammaBrick ℓ)` which is what makes
the drift term cost a factor `4` and nothing more.  `1383840 = 4·345960`. -/

theorem sharpFloorConst_eq_at_zero {ell : ℕ} (hell : 0 < ell) (σ₀ : ℝ) :
    sharpFloorConst (gammaBrick ell) 0 σ₀ = gammaBrick ell / σ₀ ^ 2 := by
  unfold sharpFloorConst
  rw [sub_zero, div_pow, Real.sq_sqrt (le_of_lt (gammaBrick_pos hell))]

theorem sharpFloorConst_lower_at_zero {ell : ℕ} (hell : 0 < ell) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    1 / (345960 * (ell : ℝ) ^ 6 * σ₀ ^ 2) ≤ sharpFloorConst (gammaBrick ell) 0 σ₀ := by
  rw [sharpFloorConst_eq_at_zero hell σ₀]
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hlow := gammaBrick_lower hell
  have hd : (0 : ℝ) < σ₀ ^ 2 := by positivity
  have he : (0 : ℝ) < 345960 * (ell : ℝ) ^ 6 := by positivity
  rw [div_le_div_iff₀ (by positivity) hd]
  rw [div_le_iff₀ he] at hlow
  nlinarith [hlow, hd, he]

/-- **THE CONSTANT UNDER THE HALF-DRIFT HYPOTHESIS.**  `κ ≤ ½√(gammaBrick ℓ)` gives
`sharpFloorConst ≥ gammaBrick ℓ/(4σ₀²) ≥ 1/(1383840·ℓ⁶·σ₀²)`.  The `4` is the ONLY price the drift
term charges in this regime, and it is derived (`(√γ − κ)² ≥ (√γ/2)² = γ/4`), not chosen. -/
theorem sharpFloorConst_lower_halfDrift {ell : ℕ} (hell : 0 < ell) (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀)
    (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaBrick ell) / 2) :
    1 / (1383840 * (ell : ℝ) ^ 6 * σ₀ ^ 2) ≤ sharpFloorConst (gammaBrick ell) κ σ₀ := by
  have hγ : 0 < gammaBrick ell := gammaBrick_pos hell
  have hs : Real.sqrt (gammaBrick ell) ^ 2 = gammaBrick ell :=
    Real.sq_sqrt (le_of_lt hγ)
  have hs0 : 0 ≤ Real.sqrt (gammaBrick ell) := Real.sqrt_nonneg _
  have hgap : Real.sqrt (gammaBrick ell) / 2 ≤ Real.sqrt (gammaBrick ell) - κ := by
    linarith
  have hgap0 : (0 : ℝ) ≤ Real.sqrt (gammaBrick ell) / 2 := by linarith
  have hquart : gammaBrick ell / 4
      ≤ (Real.sqrt (gammaBrick ell) - κ) ^ 2 := by
    nlinarith [hgap, hgap0, hs]
  have hlow := gammaBrick_lower hell
  have hd : (0 : ℝ) < σ₀ ^ 2 := by positivity
  have he : (0 : ℝ) < 345960 * (ell : ℝ) ^ 6 := by positivity
  rw [div_le_iff₀ he] at hlow
  unfold sharpFloorConst
  rw [div_pow, div_le_div_iff₀ (by positivity) hd]
  have h1 : gammaBrick ell / 4 * (1383840 * (ell : ℝ) ^ 6)
      ≤ (Real.sqrt (gammaBrick ell) - κ) ^ 2 * (1383840 * (ell : ℝ) ^ 6) :=
    mul_le_mul_of_nonneg_right hquart (by positivity)
  have h2 : gammaBrick ell / 4 * (1383840 * (ell : ℝ) ^ 6)
      = gammaBrick ell * (345960 * (ell : ℝ) ^ 6) := by ring
  rw [h2] at h1
  have hkey : (1 : ℝ) ≤ (Real.sqrt (gammaBrick ell) - κ) ^ 2 * (1383840 * (ell : ℝ) ^ 6) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hd)
  nlinarith [hmul]

/-! ### §8b — THE THRESHOLD, SOLVED FOR THE LINK DEVIATION, IN EXACT RATIONALS

`R = N·495·δ` with `N` the source lane's `‖T‖·√(2|Bond L|)`; the threshold is `2‖H₁‖c₂R < γ₁`.
`2·495 = 990`, and `990·1383840 = 1370001600`, so the admissible deviation is

    δ  <  1 / (1370001600 · ℓ⁶ · σ₀² · ‖H₁‖ · c₂ · N) .

Every factor is counted: `495` and the `√(2|Bond L|)` are `SourceWiredJ`'s (GRADE 3), `2` is the
printed `−2⟨H₁D̃⁽²⁾,J⟩`, `1383840 = 4·345960` is §8a's, `345960 = 12454560/36` is
`TerminalCompose.gammaBrick_lower`'s. -/
theorem delta_threshold_suffices {ell : ℕ} (hell : 0 < ell) (σ₀ H1 c₂ N δ : ℝ)
    (hσ₀ : 0 < σ₀) (hH1 : 0 < H1) (hc₂ : 0 < c₂) (hN : 0 < N) (hδ0 : 0 ≤ δ)
    -- `hδ0` is RETAINED DELIBERATELY and is not used by the proof: at `δ < 0` the left-hand side is
    -- negative and the statement holds trivially, i.e. its truth there rests on a sign accident
    -- rather than on the intended regime.  Same practice as
    -- `TerminalCompose.gammaBrick_le_coefficient`'s `hell`.
    (hδ : δ < 1 / (1370001600 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * H1 * c₂ * N)) :
    2 * H1 * c₂ * (N * (495 * δ)) < 1 / (1383840 * (ell : ℝ) ^ 6 * σ₀ ^ 2) := by
  have he : (0 : ℝ) < (ell : ℝ) ^ 6 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  have hden : (0 : ℝ) < 1370001600 * (ell : ℝ) ^ 6 * σ₀ ^ 2 * H1 * c₂ * N := by positivity
  have hden2 : (0 : ℝ) < 1383840 * (ell : ℝ) ^ 6 * σ₀ ^ 2 := by positivity
  rw [lt_div_iff₀ hden] at hδ
  rw [lt_div_iff₀ hden2]
  nlinarith [hδ, he, hσ₀, hH1, hc₂, hN, mul_pos hH1 hc₂, sq_nonneg σ₀]

/-- **§8c — THE HEADLINE, WIRED TO THE PRINTED SOURCE.**

Everything of §8 composed, with the source instantiated at the configuration's OWN `J(U)` carried
into the `A`-space by a bounded `T`, and the smallness expressed as a closed-form bound on the link
deviation `δ`:

    ℓ ≥ 2, tiled torus, α₁ ≤ 1/(186ℓ³), (3.128), the drift-priced chain bound,
    κ ≤ ½√(gammaBrick ℓ),  δ < 1/(1370001600·ℓ⁶·σ₀²·‖H₁‖·c₂·(‖T‖√(2|Bond L|)))
    ⟹  ⟨B̃, C*Δ_k(U)C B̃⟩ > 0  for every B̃ ≠ 0 in ℓ²(Λ̃).

The `‖H₁‖` slot is bounded at THIS datum by §4e — it is not the collapsed witness's `≤ 1`. -/
theorem terminal_wired_posDef {ell : ℕ} (hell2 : 2 ≤ ell)
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
    0 < cdcFormTrue D bc Qext (T (JsuTwo U)) U ell (dinvC U ell) w := by
  have hell : 0 < ell := by omega
  have hs0 : (0 : ℝ) ≤ Real.sqrt (gammaBrick ell) := Real.sqrt_nonneg _
  have hκγ : κ ≤ Real.sqrt (gammaBrick ell) := by linarith
  set N : ℝ := Real.sqrt (2 * (Fintype.card (Bond L))) with hN
  have hNpos : 0 < N := by
    rw [hN]
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (Fintype.card (Bond L) : ℝ) := by exact_mod_cast hcard
    linarith
  -- the source bound, from `SourceWiredComposed` (GRADE 3), reused
  have hJ : ‖T (JsuTwo U)‖ ≤ ‖T‖ * (N * (495 * δ)) := norm_source_le_of_linkDev T U hU
  -- the arithmetic
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
  have hsmall : 2 * ‖solutionOperator D‖ * c₂ * ‖T (JsuTwo U)‖
      < sharpFloorConst (gammaBrick ell) κ σ₀ := by linarith
  exact terminal_printed_posDef hell2 hstrict hdvd U hthr D bc d pen hform σ₀ κ hσ₀ hκ hκγ hraw
    Qext (T (JsuTwo U)) S hS c₂ (le_of_lt hc₂) hD2 hsmall w hw

#print axioms deltaKQuadForm_eq_inner_deltaKQuadOp
#print axioms terminal_printed_posDef
#print axioms sharpFloorConst_eq_at_zero
#print axioms sharpFloorConst_lower_at_zero
#print axioms sharpFloorConst_lower_halfDrift
#print axioms delta_threshold_suffices
#print axioms terminal_wired_posDef

end AdalyFormal.Balaban.TerminalAssembly

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM dstarDLM inner_dstarDLM_symm)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick)
open AdalyFormal.HBaseInputs.CovData (build build_Q build_Ginv)

variable {L : PeriodicLatticeExtent}

/-! ## §9 — THE HYPOTHESIS SET IS SIMULTANEOUSLY INHABITED, AT EVERY BACKGROUND

`compute/schur_floor/SCOPE.md` (§5 item 2 of `SchurFloor.lean`'s header) records that **no
simultaneous inhabitant of the concrete composition was exhibited**.  §9 exhibits one for the two
COVARIANCE-side hypotheses of §8 — `hform` (3.128) and `hraw` — and does so at EVERY background `U`,
curved included, with the drift coefficient `κ = 0`.

The datum is `Ginv := D_U^*D_U + a·I`, `Q := I`, built with `CovDataCtor.build` (REUSED, LAW-19).
**§9d states its cost with the same force: `Q = I` is the collapse, so at THIS datum
`(QG₁Q*)⁻¹ = G₁⁻¹` and the composed floor is the brick and nothing more.**  It is a non-vacuity
witness, not Bałaban's geometry — exactly the standing of `DeltaKWiring.bondData`, whose
`collapsed_Q_bijective` costs the same collapse explicitly. -/

/-- `Ginv := D_U^*D_U + a·I` on the printed carrier. -/
noncomputable def assemblyGinv
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (a : ℝ) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  dstarDCLM U + a • (ContinuousLinearMap.id ℝ (BondFnL2 L))

theorem inner_assemblyGinv
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (a : ℝ)
    (x : BondFnL2 L) :
    (inner ℝ x (assemblyGinv U a x) : ℝ) = ‖curlCovariantCLM_L2 U x‖ ^ 2 + a * ‖x‖ ^ 2 := by
  show (inner ℝ x ((dstarDCLM U + a • (ContinuousLinearMap.id ℝ (BondFnL2 L))) x) : ℝ) = _
  rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.smul_apply,
    real_inner_smul_right]
  show (inner ℝ x (dstarDCLM U x) : ℝ) + a * (inner ℝ x x : ℝ) = _
  rw [normSq_curlCLM_eq_dstarDCLM_form, real_inner_self_eq_norm_sq]

theorem assemblyGinv_selfAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (a : ℝ)
    (x y : BondFnL2 L) :
    (inner ℝ (assemblyGinv U a x) y : ℝ) = inner ℝ x (assemblyGinv U a y) := by
  show (inner ℝ ((dstarDCLM U + a • (ContinuousLinearMap.id ℝ (BondFnL2 L))) x) y : ℝ)
    = inner ℝ x ((dstarDCLM U + a • (ContinuousLinearMap.id ℝ (BondFnL2 L))) y)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  show (inner ℝ (dstarDLM U x) y : ℝ) + a * (inner ℝ x y : ℝ)
    = (inner ℝ x (dstarDLM U y) : ℝ) + a * (inner ℝ x y : ℝ)
  rw [inner_dstarDLM_symm]

theorem assemblyGinv_posDef
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (x : BondFnL2 L) (hx : x ≠ 0) : (0 : ℝ) < inner ℝ x (assemblyGinv U a x) := by
  rw [inner_assemblyGinv]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have : (0 : ℝ) ≤ ‖curlCovariantCLM_L2 U x‖ ^ 2 := sq_nonneg _
  nlinarith [this, mul_pos ha (pow_pos hn 2)]

/-- **THE WITNESS DATUM**, at every background and every `a > 0`. -/
noncomputable def assemblyDatum
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    BalabanCovarianceData (BondFnL2 L) (BondFnL2 L) :=
  build (assemblyGinv U a) (ContinuousLinearMap.id ℝ (BondFnL2 L))
    (assemblyGinv_selfAdjoint U a) (assemblyGinv_posDef U ha) (fun y => ⟨y, rfl⟩)

theorem assemblyDatum_Q
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    (assemblyDatum U ha).Q = ContinuousLinearMap.id ℝ (BondFnL2 L) := rfl

theorem assemblyDatum_Ginv
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    (assemblyDatum U ha).Ginv = assemblyGinv U a := rfl

theorem assemblyDatum_Qstar
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (x : BondFnL2 L) : (assemblyDatum U ha).Qstar x = x := by
  show ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ (BondFnL2 L)) x = x
  rw [ContinuousLinearMap.adjoint_id]
  rfl

/-- **§9a — (3.128) HOLDS AT THE WITNESS DATUM, AT EVERY BACKGROUND**, with `d = ∂_U` the covariant
coboundary, `pen = 0`, and the SAME `a`.  An EQUALITY of forms, not an estimate. -/
theorem assemblyDatum_isPrintedG1Form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    IsPrintedG1Form (assemblyDatum U ha) a (curlCovariantCLM_L2 U)
      (0 : BondFnL2 L →L[ℝ] BondFnL2 L) := by
  intro A
  rw [assemblyDatum_Ginv U ha, inner_assemblyGinv]
  show _ = ‖curlCovariantCLM_L2 U A‖ ^ 2 + ‖(0 : BondFnL2 L)‖ ^ 2
      + a * ‖(assemblyDatum U ha).Q A‖ ^ 2
  rw [assemblyDatum_Q U ha, norm_zero]
  show _ = ‖curlCovariantCLM_L2 U A‖ ^ 2 + 0 ^ 2 + a * ‖A‖ ^ 2
  ring

/-- **§9b — `hraw` HOLDS AT THE WITNESS DATUM, AT EVERY BACKGROUND, WITH `σ₀ = 1` AND `κ = 0`.**
An EQUALITY: `Q = I` makes the chain bound trivial.  So the drift coefficient is `0` here, and the
half-drift hypothesis `κ ≤ ½√(gammaBrick ℓ)` of §8c is met with room to spare. -/
theorem assemblyDatum_hraw
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U ((assemblyDatum U ha).Q A)‖
      ≤ 1 * ‖curlCovariantCLM_L2 U A‖ + 0 * ‖(assemblyDatum U ha).Q A‖ := by
  rw [assemblyDatum_Q U ha]
  show ‖curlCovariantCLM_L2 U A‖ ≤ 1 * ‖curlCovariantCLM_L2 U A‖ + 0 * ‖A‖
  ring_nf
  exact le_refl _

/-- **§9c — THE TWO COVARIANCE-SIDE HYPOTHESES OF §8, TOGETHER, AT EVERY BACKGROUND.**  This is the
row `SchurFloor` §5 item 2 says is missing.  Note what it does NOT contain: no smallness on `U`, no
`ell`, no source — those enter §8 separately and are inhabited there by `TerminalCompose`'s own
curved-background row (`witness_background_curved_and_in_class`) and by `SourceWiredJ`. -/
theorem assembly_covariance_hypotheses_inhabited
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    IsPrintedG1Form (assemblyDatum U ha) a (curlCovariantCLM_L2 U)
        (0 : BondFnL2 L →L[ℝ] BondFnL2 L)
    ∧ (∀ A : BondFnL2 L, ‖curlCovariantCLM_L2 U ((assemblyDatum U ha).Q A)‖
        ≤ 1 * ‖curlCovariantCLM_L2 U A‖ + 0 * ‖(assemblyDatum U ha).Q A‖) :=
  ⟨assemblyDatum_isPrintedG1Form U ha, assemblyDatum_hraw U ha⟩

/-! ### §9d — WHAT THE WITNESS COSTS, STATED AS THEOREMS

Two facts, both negative, both proved rather than described. -/

/-- **THE SCHUR COMPLEMENT COLLAPSES WHEN `Q = I`.**  `(QG₁Q*)⁻¹ = G₁⁻¹` at any datum whose `Q` and
`Q*` are the identity — from `Comp_eq`, `Comp_CompInv` and `Ginv_Gstar` alone, so it is a fact about
the STRUCTURE and not about this particular `Ginv`. -/
theorem compInv_eq_Ginv_of_Q_id {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : BalabanCovarianceData H H) (hQ : ∀ x : H, D.Q x = x) (hQs : ∀ x : H, D.Qstar x = x)
    (B : H) : D.CompInv B = D.Ginv B := by
  have hc : D.Gstar (D.CompInv B) = B := by
    have h := D.Comp_CompInv B
    rw [D.Comp_eq (D.CompInv B), hQs (D.CompInv B), hQ (D.Gstar (D.CompInv B))] at h
    exact h
  calc D.CompInv B = D.Ginv (D.Gstar (D.CompInv B)) := (D.Ginv_Gstar (D.CompInv B)).symm
    _ = D.Ginv B := by rw [hc]

/-- **THE COST, EXHIBITED: AT THE WITNESS DATUM THE COMPOSED FLOOR *IS* THE BRICK.**

`Φ_a(B) = ⟨B,(QG₁Q*)⁻¹B⟩ − a‖B‖² = ‖∂_U B‖² = ⟨B, D_U^*D_U B⟩` — the very object
`TerminalCompose.cdc_floor_class_uniform` already bounds.  So §8, instantiated at THIS datum, proves
nothing beyond the brick plus the source-term accounting; the terminal statement's content at a
FAITHFUL datum rests entirely on `hraw` there, which is `[STOKES-COMM-U]` at the level pair the tree
cannot express (`compute/terminal_compose/DAG.md` row G14).  This theorem exists so that fact cannot
be read off anything softer than an equality. -/
theorem assemblyDatum_deltaKQuadForm_eq_curl_energy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (B : BondFnL2 L) :
    deltaKQuadForm (assemblyDatum U ha) a B = ‖curlCovariantCLM_L2 U B‖ ^ 2 := by
  show (inner ℝ B ((assemblyDatum U ha).CompInv B) : ℝ) - a * ‖B‖ ^ 2 = _
  rw [compInv_eq_Ginv_of_Q_id (assemblyDatum U ha) (fun x => rfl) (assemblyDatum_Qstar U ha) B,
    assemblyDatum_Ginv U ha, inner_assemblyGinv]
  ring

/-- **AND `Q` IS BIJECTIVE**, i.e. the witness pays `DeltaKWiring.collapsed_Q_bijective`'s price:
the minimisation `Φ_a(B) = min{⟨A,G₁⁻¹A⟩ : QA = B}` is over a SINGLE point, so nothing variational
happens at this datum. -/
theorem assemblyDatum_Q_bijective
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a) :
    Function.Bijective (assemblyDatum U ha).Q :=
  ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

#print axioms assemblyGinv
#print axioms inner_assemblyGinv
#print axioms assemblyGinv_selfAdjoint
#print axioms assemblyGinv_posDef
#print axioms assemblyDatum
#print axioms assemblyDatum_Q
#print axioms assemblyDatum_Ginv
#print axioms assemblyDatum_Qstar
#print axioms assemblyDatum_isPrintedG1Form
#print axioms assemblyDatum_hraw
#print axioms assembly_covariance_hypotheses_inhabited
#print axioms compInv_eq_Ginv_of_Q_id
#print axioms assemblyDatum_deltaKQuadForm_eq_curl_energy
#print axioms assemblyDatum_Q_bijective

end AdalyFormal.Balaban.TerminalAssembly

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply)
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUDomainWitness (frobSupBond_trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue norm_cZero_pos bondQext
  bondDtilde2)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo norm_JsuTwo_le)
open AdalyFormal.Balaban.SourceWired (LinkDev)

variable {Hs : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
variable {L : PeriodicLatticeExtent}

/-! ## §10 — THE HEADLINE PARAMETRISED BY THE SOURCE BOUND, AND THE WITNESS'S OWN CONSTANTS

Two repairs to §8/§9 that this lane can make without new machinery, and one end-to-end row.

**§10a** removes `LinkDev` from the headline's hypothesis list.  `LinkDev` is `source_wired`'s
GLOBAL-gauge class, and `compute/gauge_patching/` §4 PROVES the printed per-cube class is strictly
weaker — so a theorem stated on `LinkDev` is stated on a class the source does not grant.  The bound
on `‖J‖` is the only thing the composition consumes, and `gauge_patching`'s
`norm_JsuTwo_le_of_locGaugeDev` supplies it from the printed per-cube data **with the identical
constant**.  Parametrising by the bound therefore lets either supplier feed the same theorem. -/

/-- **§10a — THE HEADLINE, WITH THE SOURCE ENTERING ONLY THROUGH A BOUND.**  `hJbound` is exactly
what `SourceWiredComposed.norm_source_le_of_linkDev` (global gauge) and
`GaugePatching.norm_JsuTwo_le_of_locGaugeDev` (the printed per-cube class) both deliver. -/
theorem terminal_posDef_of_source_bound {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hthr : frobSupBond U ≤ 1 / (186 * (ell : ℝ) ^ 3))
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : BalabanCovarianceData Hs (BondFnL2 L)) (bc : BaseConstant)
    (d : Hs →L[ℝ] P₁) (pen : Hs →L[ℝ] P₃)
    (hform : IsPrintedG1Form D (usedAt bc 0) d pen)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaBrick ell) / 2)
    (hraw : ∀ A : Hs, ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
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
  exact terminal_printed_posDef hell2 hstrict hdvd U hthr D bc d pen hform σ₀ κ hσ₀ hκ hκγ hraw
    Qext J S hS c₂ hc₂ hD2 hsmall w hw

/-! ### §10b — THE WITNESS DATUM'S OWN `H₁`, AND ITS NORM FROM BELOW

§4e bounds `‖H₁‖` from ABOVE at any datum.  At the §9 witness `H₁` is computed exactly, which both
discharges the headline's `0 < ‖H₁‖` binder and exhibits the collapse a second way. -/

/-- **`H₁ = I` AT THE WITNESS DATUM.**  From `Qstar = I` and `CompInv = Ginv` (§9d), through
`Gstar_Ginv`.  Nothing about `D_U^*D_U` is used, so this is a consequence of `Q = I` alone. -/
theorem assemblyDatum_H1_eq_id
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (B : BondFnL2 L) : solutionOperator (assemblyDatum U ha) B = B := by
  rw [solutionOperator_apply, assemblyDatum_Qstar U ha,
    compInv_eq_Ginv_of_Q_id (assemblyDatum U ha) (fun x => rfl) (assemblyDatum_Qstar U ha) B]
  exact (assemblyDatum U ha).Gstar_Ginv B

/-- **`1 ≤ ‖H₁‖` AT THE WITNESS DATUM**, hence `0 < ‖H₁‖` — the headline's non-degeneracy binder,
discharged from ONE nonzero vector of the carrier rather than from a `Nontrivial` instance. -/
theorem one_le_norm_H1_assembly
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (B₀ : BondFnL2 L) (hB₀ : B₀ ≠ 0) : 1 ≤ ‖solutionOperator (assemblyDatum U ha)‖ := by
  have hn : 0 < ‖B₀‖ := norm_pos_iff.mpr hB₀
  have hle := (solutionOperator (assemblyDatum U ha)).le_opNorm B₀
  rw [assemblyDatum_H1_eq_id U ha B₀] at hle
  nlinarith [hle, hn, norm_nonneg (solutionOperator (assemblyDatum U ha))]

/-- The carrier has a named nonzero element at the printed parameters, so §10b's binder is met:
`C₀` of `construct_cdc`'s own `tildeSpike`.  Reuses `DeltaKWiring.norm_cZero_pos` (LAW-19). -/
theorem cZero_ne_zero_of_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0) :
    cZero U ell Dinv w ≠ 0 := norm_pos_iff.mp (norm_cZero_pos U Dinv w hw)

/-! ### §10c — THE SOURCE OPERATOR AT THE WITNESS DATUM, AND ONE END-TO-END ROW

`deltak_wiring`'s `bondQext v` is the printed `D̃⁽²⁾` shape; at the witness datum `H₁ = I`, so the
source operator is the scalar `⟪v,J⟫·I`.  Both `IsSourceOperator` and `hD2` are then theorems. -/

theorem assemblyDatum_isSourceOperator
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 < a)
    (v J : BondFnL2 L) :
    IsSourceOperator (assemblyDatum U ha) (bondQext v) J
      ((inner ℝ v J : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) := by
  intro B
  show (inner ℝ B (((inner ℝ v J : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) B) : ℝ)
    = (inner ℝ (solutionOperator (assemblyDatum U ha)
        (Dtilde2Shape (bondQext v) B)) J : ℝ)
  rw [bondDtilde2, assemblyDatum_H1_eq_id U ha, real_inner_smul_left]
  show (inner ℝ B ((inner ℝ v J : ℝ) • B) : ℝ) = _
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem assemblyDatum_hD2 (v B : BondFnL2 L) :
    ‖Dtilde2Shape (bondQext v) B‖ ≤ ‖v‖ * ‖B‖ ^ 2 := by
  rw [bondDtilde2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_of_eq (by ring)

/-- **THE FLAT BACKGROUND IS IN EVERY SMALLNESS CLASS AND HAS `LinkDev 0`.** -/
theorem trivialU_in_class {ell : ℕ} (hell : 0 < ell) :
    frobSupBond (trivialU L) ≤ 1 / (186 * (ell : ℝ) ^ 3) ∧ LinkDev 0 (trivialU L) := by
  have hpos : (0 : ℝ) < 186 * (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  refine ⟨?_, ?_⟩
  · rw [frobSupBond_trivialU]
    positivity
  · intro b i j
    show ‖(((trivialU L b : Matrix (Fin 2) (Fin 2) ℂ) - 1) i j)‖ ≤ 0
    have h1 : ((trivialU L b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1
      rfl
    rw [h1, sub_self]
    simp

/-- **ONE END-TO-END ROW, WITH EVERY BINDER OF §10a DISCHARGED.**

At the flat background, at the §9 witness datum, with `ell ≥ 2` on a tiled torus, `a > 0`, a nonzero
`v` and the printed `D̃⁽²⁾` shape: the printed `C*Δ_kC` is positive definite on `ℓ²(Λ̃)`.

**⚠ WHAT THIS ROW IS AND IS NOT — read before quoting it.**  Two things collapse here and both are
theorems elsewhere in this module, not opinions:
1. `Q = I` (`assemblyDatum_Q_bijective`), so `Φ_a` is the curl energy
   (`assemblyDatum_deltaKQuadForm_eq_curl_energy`) and the floor is the brick.
2. `δ = 0` at `U = 1` (`trivialU_in_class`), so `‖J(U)‖ ≤ 0` and **the source term contributes
   nothing** — precisely the degeneracy `SourceWiredComposed` §6 warns about.
So this row establishes that the hypothesis set of §10a is SIMULTANEOUSLY SATISFIABLE with every
binder discharged, and nothing more.  A row at a CURVED background needs a configuration with a
SMALL `LinkDev`, and the tree carries only the unconditional `LinkDev 2` (`linkDev_two`) plus
`frobSupBond`-smallness, which is a different norm; that is residual 4 of `SCOPE.md` §7.

**`hv : v ≠ 0` IS NOT USED BY THIS PROOF AND IS RETAINED DELIBERATELY** (linter-flagged, and flagged
independently by a nested validator).  At `v = 0` the statement is still TRUE — but only because
`c₂ = ‖v‖ = 0` makes the source operator identically `0`, i.e. its truth there rests on the SECOND
degeneracy this docstring already warns about, doubled.  The binder stays so that the row cannot be
quoted as an instance in which the source term is present. -/
theorem end_to_end_flat {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (bc : BaseConstant) (ha : 0 < usedAt bc 0) (v : BondFnL2 L) (hv : v ≠ 0)
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue (assemblyDatum (trivialU L) ha) bc (bondQext v)
        (JsuTwo (trivialU L)) (trivialU L) ell (dinvC (trivialU L) ell) w := by
  have hell : 0 < ell := by omega
  obtain ⟨hthr, hlink⟩ := trivialU_in_class (L := L) hell
  have hJ0 : ‖JsuTwo (trivialU L)‖ ≤ 0 := by
    have := norm_JsuTwo_le (trivialU L) hlink
    simpa using this
  have hγ : 0 < gammaBrick ell := gammaBrick_pos hell
  have hsharp : sharpFloorConst (gammaBrick ell) 0 1 = gammaBrick ell := by
    rw [sharpFloorConst_eq_at_zero hell 1]
    norm_num
  refine terminal_posDef_of_source_bound hell2 hstrict hdvd (trivialU L) hthr
    (assemblyDatum (trivialU L) ha) bc (curlCovariantCLM_L2 (trivialU L))
    (0 : BondFnL2 L →L[ℝ] BondFnL2 L) (assemblyDatum_isPrintedG1Form (trivialU L) ha)
    1 0 one_pos le_rfl (by positivity) (assemblyDatum_hraw (trivialU L) ha)
    (bondQext v) (JsuTwo (trivialU L)) _ (assemblyDatum_isSourceOperator (trivialU L) ha v _)
    ‖v‖ (norm_nonneg v) (assemblyDatum_hD2 v) 0 hJ0 ?_ w hw
  rw [hsharp]
  simpa using hγ

#print axioms terminal_posDef_of_source_bound
#print axioms assemblyDatum_H1_eq_id
#print axioms one_le_norm_H1_assembly
#print axioms cZero_ne_zero_of_ne_zero
#print axioms assemblyDatum_isSourceOperator
#print axioms assemblyDatum_hD2
#print axioms trivialU_in_class
#print axioms end_to_end_flat

end AdalyFormal.Balaban.TerminalAssembly

namespace AdalyFormal.Balaban.TerminalAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.Gamma1Positive (deltaKQuadForm)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero tildeSpike)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos witL3_hyps
  tildeSpike_witL3_ne_zero witness_background_curved_and_in_class)
open AdalyFormal.Balaban.CovLemma24Witness (witU witT witU_alpha_le_threshold)
open AdalyFormal.Balaban.DeltaKWiring (norm_cZero_pos)

/-! ## §11 — THE FLOOR HALF AT A GENUINELY CURVED BACKGROUND

`end_to_end_flat` (§10c) discharges every binder but does so at `U = 1`, where the source vanishes.
The reason it is not run at a curved background is arithmetic and is worth stating exactly: the
SOURCE threshold `δ < 1/(1370001600·ℓ⁶·σ₀²·‖H₁‖·c₂·N)` is smaller than the COVARIANCE class
`α₁ ≤ 1/(186·ℓ³)` by more than nine orders of magnitude at `ℓ = 3`, and the tree's curved witness
`CovLemma24Witness.witU witT` was built to the SECOND of those, not the first.  No configuration in
the tree is proved to satisfy the first with a curvature that is nonzero.

What CAN be run at a curved background is the whole FLOOR half — everything except the source term —
and that is done here, with a STRICTLY POSITIVE left-hand side on a NAMED nonzero element of the
printed carrier (S82: not read off `B̃ = 0`). -/

/-- **THE COMPOSED SCHUR FLOOR AT A CURVED BACKGROUND, NON-VACUOUSLY.**

At `ℓ = 3` on the `9³` torus, at `CovLemma24Witness.witU witT` — a background with plaquette holonomy
`≠ 1` and `α₁ > 0` (`TerminalCompose.witness_background_curved_and_in_class`, CITED) — at the §9
witness datum, on `construct_cdc`'s own named nonzero element of `ℓ²(Λ̃)`:

    0  <  gammaBrick 3 · ‖C₀B̃‖²  ≤  ⟨C₀B̃, (Q G₁ Q*)⁻¹ C₀B̃⟩ − a‖C₀B̃‖² .

Both conjuncts matter: the second is the floor, the first rules out the degenerate reading
`0 ≤ something`. -/
theorem schur_floor_curved_nonvacuous {a : ℝ} (ha : 0 < a) :
    0 < sharpFloorConst (gammaBrick 3) 0 1
        * ‖cZero (witU witT) 3 (dinvC (witU witT) 3)
            (tildeSpike (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
              (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)‖ ^ 2
    ∧ sharpFloorConst (gammaBrick 3) 0 1
        * ‖cZero (witU witT) 3 (dinvC (witU witT) 3)
            (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)‖ ^ 2
      ≤ deltaKQuadForm (assemblyDatum (witU witT) ha) a
          (cZero (witU witT) 3 (dinvC (witU witT) 3)
            (tildeSpike (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)) := by
  have hγ : 0 < gammaBrick 3 := gammaBrick_pos (by norm_num)
  have hsharp : sharpFloorConst (gammaBrick 3) 0 1 = gammaBrick 3 := by
    rw [sharpFloorConst_eq_at_zero (by norm_num : 0 < 3) 1]
    norm_num
  have hne : cZero (witU witT) 3 (dinvC (witU witT) 3)
      (tildeSpike (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
        (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2) ≠ 0 :=
    cZero_ne_zero_of_ne_zero _ _ _ tildeSpike_witL3_ne_zero
  have hn : 0 < ‖cZero (witU witT) 3 (dinvC (witU witT) 3)
      (tildeSpike (L := AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
        (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.2)‖ := norm_pos_iff.mpr hne
  refine ⟨by rw [hsharp]; positivity, ?_⟩
  exact schur_floor_hraw_at_cZero (by norm_num : (2 : ℕ) ≤ 3) witL3_hyps.1 witL3_hyps.2
    (witU witT) witU_alpha_le_threshold (assemblyDatum (witU witT) ha) a
    (curlCovariantCLM_L2 (witU witT)) (0 : BondFnL2 AdalyFormal.Balaban.Lemma24GeneralEll.witL3 →L[ℝ]
      BondFnL2 AdalyFormal.Balaban.Lemma24GeneralEll.witL3)
    (assemblyDatum_isPrintedG1Form (witU witT) ha) 1 0 one_pos le_rfl
    (by positivity) (assemblyDatum_hraw (witU witT) ha) _

/-- **THE BACKGROUND OF §11 IS CURVED**, re-exposed so the row above cannot be read as a `U = 1`
statement in disguise.  CITED from `TerminalCompose`, not rebuilt. -/
theorem schur_floor_curved_background_is_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witU witT)
        (AdalyFormal.Balaban.CovLemma24Witness.witBond.1,
         AdalyFormal.Balaban.CovLemma24Witness.witDir)
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    ∧ 0 < AdalyFormal.Balaban.RegularUPerturbation.frobSupBond (witU witT) :=
  ⟨witness_background_curved_and_in_class.1, witness_background_curved_and_in_class.2.1⟩

#print axioms schur_floor_curved_nonvacuous
#print axioms schur_floor_curved_background_is_curved

end AdalyFormal.Balaban.TerminalAssembly
