/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import ConstructCDC
import AdalyFormal.Balaban.DeltaKAssembly

set_option autoImplicit false

/-!
# WIRING THE PRINTED `Δ_k` (CMP99b (3.156)) INTO `construct_cdc`'s DOMAIN MACHINERY

`compute/construct_cdc/` built `C^*Δ_kC` on the printed carrier `ℓ²(Λ̃)` but with
`Δ_k := dstarDCLM U + T2`, which its own `SCOPE.md` §3/§4 ties to CMP99b **(3.10)** — a different,
earlier, non-recursive operator (`compute/s3_adjudication/PROGRESS.md`, Step 3). The printed `Δ_k`
of **(3.156)** has three additive terms and is carried, in this tree, only by
`DeltaKAssembly.deltaKForm` — which was instantiated only at a toy `EuclideanSpace ℝ (Fin 1)`
witness and was never restricted to the printed subspace.

This module composes the two: `deltaKForm` at the **true bond carrier**, restricted to the printed
subspace by `construct_cdc`'s `cZero`, and identified with `construct_cdc`'s `cdcOp`.

## §0 — THE CARRIER, FIXED BY THE PAGE (not chosen)

`corpus/pages/CMP99b_p428.md` (`verification_status: adjudicated`) prints (3.156) and then
*"This form is considered on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q_1B=0}`"*, and
(3.159) on the same page prints the integral with `δ(Q_1B)` on `B` and `δ(QA-B)` on `A`. So there
are THREE levels: the `A`-space, the `B`-space (unit lattice `Λ`), and `Λ'`. `Q` maps `A`-space to
`B`-space, `Q_1` maps `B`-space to `Λ'`. Hence in `BalabanCovarianceData H K`:

* `K` := the `B`-space := `BondFnL2 L` — the space `(QG_1Q^*)^{-1}` acts on, the space `B` ranges
  over, the space the printed subspace lives in, and `cZero`'s codomain. **THE TRUE BOND CARRIER.**
* `H` := the `A`-space, one level finer, reached only through `H_1 : K →L H` and `J : H`. It is
  left **abstract** here: the page does not collapse it onto `K`, and §7 proves the collapse is not
  innocuous.

## §0a — WHAT IS NOT REPAIRED

The printed subspace's first clause `B = 0 on Λ^c` is **vacuous in this encoding** — the tree's
lattice is the full periodic torus, so `Λ^c = ∅`. Inherited verbatim from `construct_cdc` §5 and
from the whole `Balaban/` chain; not repairable inside one module.

`Qext` (`D̃^{(2)}`'s external parameter) and `J` remain **named parameters**, exactly as
`DeltaKAssembly` §0 findings 2 and 3 disclose: CMP99b's own `Q_j` (eq. 3.13) is blocked on the
unformalized `Ū^j` construction of [5]/CMP98, and `SourceJ.Jsource`'s carrier is the Hermitian
`𝔤^ℂ` convention, not this tree's anti-Hermitian `SuTwo`. They are NOT invented here. What §4-§6
do instead is determine what the coercivity statement's dependence on `J` actually IS.
-/

namespace AdalyFormal.Balaban.DeltaKWiring

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM)
open AdalyFormal.Balaban.ConstructCDC (TildeFn tildeExt tildeRes_tildeExt cZero cZeroStar deltaK
  deltaK_apply cdcOp inner_cdcOp_self cZero_injective cZero_mem_kerQ cZero_axialGauge
  tildeSpike tildeSpike_ne_zero)
open AdalyFormal.Balaban.DeltaKAssembly (deltaKForm taylorQuadraticTerm_sq_smul)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape taylorQuadraticTerm)
open AdalyFormal.Balaban.CovarianceG1 (gOneOfNeumann)

variable {L : PeriodicLatticeExtent}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## §1 — THE SOURCE TERM, ISOLATED, AND THE SPLIT OF (3.156) -/

/-- **The third additive term of (3.156), isolated**: `⟨H₁D̃⁽²⁾(B), J⟩`, at the true bond carrier
`K = BondFnL2 L`.  This is the term `construct_cdc`'s `Δ_k` does not have. -/
noncomputable def sourceTerm (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (B : BondFnL2 L) : ℝ :=
  (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) J : ℝ)

/-- **(3.156)'s left-hand side, split into its three printed summands**, at the true carrier. -/
theorem deltaKForm_split (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (B : BondFnL2 L) :
    deltaKForm D bc Qext J B
      = (inner ℝ B (D.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ)
        - 2 * sourceTerm D Qext J B := rfl

#print axioms sourceTerm
#print axioms deltaKForm_split

/-! ## §2 — THE `J`-FREE PART IS AN OPERATOR, UNCONDITIONALLY -/

/-- **`(QG₁Q*)⁻¹ − a·I`** — the first two summands of (3.156), as a single bounded operator on the
true bond carrier.  No hypothesis is needed: both summands are already operators. -/
noncomputable def deltaKQuadOp (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  D.CompInv - (usedAt bc 0) • (ContinuousLinearMap.id ℝ (BondFnL2 L))

theorem inner_deltaKQuadOp (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (B : BondFnL2 L) :
    (inner ℝ B (deltaKQuadOp D bc B) : ℝ)
      = (inner ℝ B (D.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ) := by
  show (inner ℝ B (D.CompInv B - (usedAt bc 0) • B) : ℝ) = _
  rw [inner_sub_right, real_inner_smul_right]

#print axioms deltaKQuadOp
#print axioms inner_deltaKQuadOp

/-! ## §3 — THE PRINTED `Δ_k` AS AN OPERATOR, AND ITS ONE NAMED HYPOTHESIS

The source term is the only summand of (3.156) that is not manifestly an operator form.  CMP99b
p.427 describes `D̃⁽²⁾` as *a quadratic polynomial in `B`*, which is exactly the statement that
`B ↦ ⟨H₁D̃⁽²⁾(B),J⟩` is the quadratic form of a bounded operator.  `Dtilde2Shape`'s Lean type
(`(K → K) → K → K`, `Qext` arbitrary) does NOT record that, so it is carried here as a hypothesis
with its referent named — never assumed silently, never invented. -/

/-- **THE NAMED RESIDUAL.**  `S` represents (3.156)'s source term as a quadratic form. -/
def IsSourceOperator (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L) : Prop :=
  ∀ B : BondFnL2 L, (inner ℝ B (S B) : ℝ) = sourceTerm D Qext J B

/-- **THE PRINTED `Δ_k`, AS AN OPERATOR**: `(QG₁Q*)⁻¹ − a·I − 2S`. -/
noncomputable def printedDeltaKOp (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  deltaKQuadOp D bc - (2 : ℝ) • S

/-- **CMP99b (3.156) ITSELF, AS A THEOREM**: `⟨B,Δ_kB⟩` equals the printed three-term left-hand
side, with `Δ_k` a genuine operator on the true bond carrier. -/
theorem inner_printedDeltaKOp (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (B : BondFnL2 L) :
    (inner ℝ B (printedDeltaKOp D bc S B) : ℝ) = deltaKForm D bc Qext J B := by
  show (inner ℝ B (deltaKQuadOp D bc B - (2 : ℝ) • S B) : ℝ) = _
  rw [inner_sub_right, real_inner_smul_right, inner_deltaKQuadOp, hS B, deltaKForm_split]

#print axioms IsSourceOperator
#print axioms printedDeltaKOp
#print axioms inner_printedDeltaKOp

/-! ### §3a — the residual, made concrete: two necessary conditions it imposes -/

/-- If the source term is an operator form then it is EVEN. -/
theorem sourceTerm_even_of_isSourceOperator (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (B : BondFnL2 L) :
    sourceTerm D Qext J (-B) = sourceTerm D Qext J B := by
  rw [← hS (-B), ← hS B, map_neg, inner_neg_neg]

/-- If the source term is an operator form then it is homogeneous of degree `2`. -/
theorem sourceTerm_homog_of_isSourceOperator (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S) (t : ℝ) (B : BondFnL2 L) :
    sourceTerm D Qext J (t • B) = t ^ 2 * sourceTerm D Qext J B := by
  rw [← hS (t • B), ← hS B, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

#print axioms sourceTerm_even_of_isSourceOperator
#print axioms sourceTerm_homog_of_isSourceOperator

/-! ## §4 — `C*Δ_kC` WITH THE **TRUE** `Δ_k`, ON THE PRINTED SUBSPACE -/

/-- **THE OBJECT THE DISPATCH ASKED FOR**: the printed (3.156) `Δ_k`-form, compressed to `ℓ²(Λ̃)`
by `construct_cdc`'s printed parametrisation `C₀`.  This is `C*Δ_kC` with the THREE-term `Δ_k`. -/
noncomputable def cdcFormTrue (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) : ℝ :=
  deltaKForm D bc Qext J (cZero U ell Dinv w)

/-- **THE THIRD GAP OF `DeltaKAssembly`, CLOSED**: the argument `C₀B̃` at which `cdcFormTrue`
evaluates the printed form lies in the printed subspace — both of its non-vacuous clauses
(`Q₁B = 0`; `B = 0` on every `Γ_{y,x}`, `y ∈ Λ'`, `x ∈ B(y)`).  Both are `construct_cdc`'s
theorems, reused (LAW-19), at the unconditional `Dinv = dinvC U ell`.  The third printed clause
`B = 0 on Λ^c` is vacuous in this encoding (§0a). -/
theorem cZero_in_printed_subspace {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (w : TildeFn L ell) :
    (∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell
        (fun b => (cZero U ell (dinvC U ell) w : BondFnL2 L) b) c = 0)
      ∧ (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
          ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
          ∀ e ∈ staircasePath y' x, (cZero U ell (dinvC U ell) w : BondFnL2 L) e = 0) :=
  ⟨fun c => cZero_mem_kerQ hell hdvd U w c, cZero_axialGauge hell hdvd U w⟩

#print axioms cdcFormTrue
#print axioms cZero_in_printed_subspace

/-! ## §5 — THE IDENTIFICATION WITH `construct_cdc`'s COERCIVITY FORM

`construct_cdc`'s `cdcOp U ell Dinv T2` is quantified over an UNCONSTRAINED `T2` (its `Δ′` leg).
The printed `Δ_k` fixes `T2` to exactly one value.  That value is computed here, the pin is proved
UNIQUE, and the resulting form is proved equal to `cdcFormTrue`. -/

/-- **THE PIN**: the one value of `construct_cdc`'s free `T2` at which its `Δ_k` is the printed one. -/
noncomputable def pinnedT2 (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  printedDeltaKOp D bc S - dstarDCLM U

theorem deltaK_pinnedT2 (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : BondFnL2 L) :
    deltaK U (pinnedT2 D bc S U) x = printedDeltaKOp D bc S x := by
  rw [deltaK_apply]
  show dstarDCLM U x + (printedDeltaKOp D bc S x - dstarDCLM U x) = _
  abel

/-- **THE PIN IS FORCED, NOT CHOSEN.** -/
theorem pinnedT2_unique (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L) :
    (∀ x : BondFnL2 L, deltaK U T2 x = printedDeltaKOp D bc S x) ↔ T2 = pinnedT2 D bc S U := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun x => ?_
    have hx : dstarDCLM U x + T2 x = printedDeltaKOp D bc S x := by
      have h0 := h x
      rw [deltaK_apply] at h0
      exact h0
    show T2 x = printedDeltaKOp D bc S x - dstarDCLM U x
    rw [← hx]; abel
  · intro h x
    rw [h]; exact deltaK_pinnedT2 D bc S U x

/-- **THE IDENTIFICATION.**  `construct_cdc`'s constructed operator `C₀*Δ_kC₀`, at the pinned `T2`,
has as its quadratic form exactly the printed (3.156) `Δ_k`-form compressed to `ℓ²(Λ̃)`.  This is
the theorem `construct_cdc` proved for (3.10)'s `Δ`, now for the printed `Δ_k`. -/
theorem inner_cdcOp_pinnedT2 (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (S : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hS : IsSourceOperator D Qext J S)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) :
    (inner ℝ w (cdcOp U ell Dinv (pinnedT2 D bc S U) w) : ℝ)
      = cdcFormTrue D bc Qext J U ell Dinv w := by
  rw [inner_cdcOp_self, deltaK_pinnedT2, inner_printedDeltaKOp D bc Qext J S hS]
  rfl

#print axioms pinnedT2
#print axioms deltaK_pinnedT2
#print axioms pinnedT2_unique
#print axioms inner_cdcOp_pinnedT2

/-! ## §6 — THE `J`-DEPENDENCE OF THE PRINTED `Δ_k`

Item 4 of the dispatch: is the coercivity statement independent of `J`?  Answered both ways. -/

/-- The source term is LINEAR in `J`. -/
theorem sourceTerm_smul_J (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (lam : ℝ) (B : BondFnL2 L) :
    sourceTerm D Qext (lam • J) B = lam * sourceTerm D Qext J B := by
  show (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) (lam • J) : ℝ) = _
  rw [real_inner_smul_right]; rfl

/-- The source term VANISHES at `J = 0`. -/
theorem sourceTerm_zero_J (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (B : BondFnL2 L) :
    sourceTerm D Qext (0 : H) B = 0 := by
  show (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) (0 : H) : ℝ) = 0
  rw [inner_zero_right]

/-- **(3.156) IS AFFINE IN `J`**, with the first two summands `J`-free. -/
theorem cdcFormTrue_affine_in_J (D : BalabanCovarianceData H (BondFnL2 L)) (bc : BaseConstant)
    (Qext : BondFnL2 L → BondFnL2 L) (J : H) (lam : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) :
    cdcFormTrue D bc Qext (lam • J) U ell Dinv w
      = (inner ℝ (cZero U ell Dinv w) (deltaKQuadOp D bc (cZero U ell Dinv w)) : ℝ)
        - 2 * lam * sourceTerm D Qext J (cZero U ell Dinv w) := by
  show deltaKForm D bc Qext (lam • J) (cZero U ell Dinv w) = _
  rw [deltaKForm_split, sourceTerm_smul_J, inner_deltaKQuadOp]
  ring

/-- **IF the source term annihilates the parametrised printed subspace, the compressed printed form
IS the `J`-free operator form** — the only circumstance in which the coercivity statement is
`J`-independent. -/
theorem cdcFormTrue_J_free_of_source_vanishes (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (h : ∀ v : TildeFn L ell, sourceTerm D Qext J (cZero U ell Dinv v) = 0)
    (w : TildeFn L ell) :
    cdcFormTrue D bc Qext J U ell Dinv w
      = (inner ℝ (cZero U ell Dinv w) (deltaKQuadOp D bc (cZero U ell Dinv w)) : ℝ) := by
  show deltaKForm D bc Qext J (cZero U ell Dinv w) = _
  rw [deltaKForm_split, h w, inner_deltaKQuadOp]
  ring

/-- **THE FAILURE, PROVED.**  If the source term is nonzero at even ONE point of the parametrised
printed subspace, then scaling `J` drives `⟨B̃, C*Δ_kC B̃⟩` below ANY prescribed real number, with
the `(QG₁Q*)⁻¹` and `a` summands untouched.  Hence no lower bound on the printed `C*Δ_kC` can be
uniform in `J`. -/
theorem cdcFormTrue_unbounded_below_in_J (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w₀ : TildeFn L ell)
    (h : sourceTerm D Qext J (cZero U ell Dinv w₀) ≠ 0) (c : ℝ) :
    ∃ lam : ℝ, cdcFormTrue D bc Qext (lam • J) U ell Dinv w₀ < c := by
  set s : ℝ := sourceTerm D Qext J (cZero U ell Dinv w₀) with hs
  set base : ℝ := (inner ℝ (cZero U ell Dinv w₀) (deltaKQuadOp D bc (cZero U ell Dinv w₀)) : ℝ)
    with hbase
  refine ⟨(base - c + 1) / (2 * s), ?_⟩
  rw [cdcFormTrue_affine_in_J]
  have h2 : 2 * ((base - c + 1) / (2 * s)) * s = base - c + 1 := by
    field_simp
  rw [← hs, ← hbase, h2]
  linarith

/-- **POSITIVE DEFINITENESS OF THE PRINTED `C*Δ_kC` FAILS FOR SOME `J`**, whenever the source term
is nonzero somewhere on the parametrised printed subspace. -/
theorem printed_cdc_not_posDef_for_some_J (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w₀ : TildeFn L ell) (hw₀ : w₀ ≠ 0)
    (h : sourceTerm D Qext J (cZero U ell Dinv w₀) ≠ 0) :
    ∃ lam : ℝ, ¬ (∀ w : TildeFn L ell, w ≠ 0 →
      (0 : ℝ) < cdcFormTrue D bc Qext (lam • J) U ell Dinv w) := by
  obtain ⟨lam, hlam⟩ := cdcFormTrue_unbounded_below_in_J D bc Qext J U Dinv w₀ h 0
  refine ⟨lam, ?_⟩
  intro hall
  exact absurd (hall w₀ hw₀) (not_lt.mpr (le_of_lt hlam))

/-! ### §6a — THE `J`-FAILURE NEEDS NO WITNESS DATA: it holds for EVERY covariance datum

`§8`'s concrete instance uses the `H = K` collapse, so a reader may ask whether the `J`-dependence
is an artifact of it.  It is not.  Everything in this subsection is for an ARBITRARY
`BalabanCovarianceData H (BondFnL2 L)` with `H` abstract. -/

/-- `BalabanCovarianceData` already forces `Q` SURJECTIVE — `CompInv` inverts
`Comp = Q∘Gstar∘Qstar`.  True of CMP99b's block average, which is onto. -/
theorem Q_surjective {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : BalabanCovarianceData H K) : Function.Surjective D.Q := by
  intro y
  refine ⟨D.Gstar (D.Qstar (D.CompInv y)), ?_⟩
  have h := D.Comp_eq (D.CompInv y)
  rw [← h, D.Comp_CompInv]

/-- `Q*` is INJECTIVE — the adjoint of a surjective map, and `Q` is surjective for every datum
(§7). -/
theorem Qstar_injective {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : BalabanCovarianceData H K) : Function.Injective D.Qstar := by
  intro y y' hyy
  have hz : ∀ z : H, (inner ℝ z (D.Qstar (y - y')) : ℝ) = 0 := by
    intro z
    have : D.Qstar (y - y') = 0 := by rw [map_sub, hyy, sub_self]
    rw [this, inner_zero_right]
  have hall : ∀ u : K, (inner ℝ u (y - y') : ℝ) = 0 := by
    intro u
    obtain ⟨z, hzu⟩ := Q_surjective D u
    rw [← hzu, D.Q_Qstar_adjoint z (y - y'), hz z]
  have := hall (y - y')
  rw [real_inner_self_eq_norm_sq] at this
  have hn : ‖y - y'‖ = 0 := by nlinarith [norm_nonneg (y - y')]
  have := sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact this

/-- **`H₁ = G₁Q*(QG₁Q*)⁻¹` IS INJECTIVE**, for every covariance datum: `Gstar` and `CompInv` are
bijective by the structure's own inverse fields, and `Qstar` is injective by the previous lemma. -/
theorem solutionOperator_injective {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : BalabanCovarianceData H K) : Function.Injective (solutionOperator D) := by
  intro y y' hyy
  rw [solutionOperator_apply, solutionOperator_apply] at hyy
  have h1 : D.Qstar (D.CompInv y) = D.Qstar (D.CompInv y') := by
    have := congrArg D.Ginv hyy
    rwa [D.Ginv_Gstar, D.Ginv_Gstar] at this
  have h2 : D.CompInv y = D.CompInv y' := Qstar_injective D h1
  have := congrArg D.Comp h2
  rwa [D.Comp_CompInv, D.Comp_CompInv] at this

/-- **THE SOURCE TERM CANNOT BE KILLED BY THE GEOMETRY**: whenever `D̃⁽²⁾(B) ≠ 0`, there is a source
`J` at which (3.156)'s third summand is nonzero — take `J := H₁D̃⁽²⁾(B)` itself.  No collapse, no
special datum, `H` abstract. -/
theorem exists_J_sourceTerm_ne_zero (D : BalabanCovarianceData H (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (B : BondFnL2 L) (h : Dtilde2Shape Qext B ≠ 0) :
    ∃ J : H, sourceTerm D Qext J B ≠ 0 := by
  refine ⟨solutionOperator D (Dtilde2Shape Qext B), ?_⟩
  show (inner ℝ (solutionOperator D (Dtilde2Shape Qext B))
    (solutionOperator D (Dtilde2Shape Qext B)) : ℝ) ≠ 0
  rw [real_inner_self_eq_norm_sq]
  have hne : solutionOperator D (Dtilde2Shape Qext B) ≠ 0 := by
    intro hz
    exact h (solutionOperator_injective D (by rw [hz, map_zero]))
  have : 0 < ‖solutionOperator D (Dtilde2Shape Qext B)‖ := norm_pos_iff.mpr hne
  positivity

/-- **THE GENERAL FAILURE.**  For EVERY covariance datum, every `Qext` whose second-order term does
not vanish at one point of the parametrised printed subspace, there is a source `J` at which the
printed `C*Δ_kC` is not positive definite.  `H` is abstract; nothing here uses the collapse. -/
theorem printed_cdc_not_posDef_general (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w₀ : TildeFn L ell) (hw₀ : w₀ ≠ 0)
    (h : Dtilde2Shape Qext (cZero U ell Dinv w₀) ≠ 0) :
    ∃ J : H, ¬ (∀ w : TildeFn L ell, w ≠ 0 →
      (0 : ℝ) < cdcFormTrue D bc Qext J U ell Dinv w) := by
  obtain ⟨J₀, hJ₀⟩ := exists_J_sourceTerm_ne_zero D Qext (cZero U ell Dinv w₀) h
  obtain ⟨lam, hlam⟩ := printed_cdc_not_posDef_for_some_J D bc Qext J₀ U Dinv w₀ hw₀ hJ₀
  exact ⟨lam • J₀, hlam⟩

/-- **EXISTENCE OF THE PRINTED `Δ_k` AS AN OPERATOR IS EQUIVALENT TO THE NAMED RESIDUAL.**  So the
hypothesis `IsSourceOperator` is not an artifact of this formulation: it is exactly what (3.156)
needs in order to define an operator at all. -/
theorem printedDeltaK_exists_iff_source_isOperator (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H) :
    (∃ A : BondFnL2 L →L[ℝ] BondFnL2 L,
        ∀ B : BondFnL2 L, (inner ℝ B (A B) : ℝ) = deltaKForm D bc Qext J B)
      ↔ (∃ S : BondFnL2 L →L[ℝ] BondFnL2 L, IsSourceOperator D Qext J S) := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨(1/2 : ℝ) • (deltaKQuadOp D bc - A), ?_⟩
    intro B
    show (inner ℝ B ((1/2 : ℝ) • (deltaKQuadOp D bc B - A B)) : ℝ) = _
    rw [real_inner_smul_right, inner_sub_right, inner_deltaKQuadOp, hA B, deltaKForm_split]
    ring
  · rintro ⟨S, hS⟩
    exact ⟨printedDeltaKOp D bc S, fun B => inner_printedDeltaKOp D bc Qext J S hS B⟩

#print axioms Qstar_injective
#print axioms solutionOperator_injective
#print axioms exists_J_sourceTerm_ne_zero
#print axioms printed_cdc_not_posDef_general
#print axioms printedDeltaK_exists_iff_source_isOperator

#print axioms sourceTerm_smul_J
#print axioms sourceTerm_zero_J
#print axioms cdcFormTrue_affine_in_J
#print axioms cdcFormTrue_J_free_of_source_vanishes
#print axioms cdcFormTrue_unbounded_below_in_J
#print axioms printed_cdc_not_posDef_for_some_J

/-! ## §7 — WHAT THE `H = K` COLLAPSE COSTS (why the theorems above keep `H` abstract) -/

/-- **THE COST.**  On the collapsed carrier `H = K = BondFnL2 L` (finite dimensional) surjectivity
upgrades to BIJECTIVITY, so `ker Q = 0` — whereas CMP99b's `Q` averages `A`-fields onto `B`-fields
and has a large kernel.  This is why every theorem of §1-§6 keeps `H` abstract; the collapse is
used ONLY in §8's non-vacuity witness, and is disclosed there. -/
theorem collapsed_Q_bijective (D : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L)) :
    Function.Bijective D.Q := by
  have hsurj : Function.Surjective (D.Q : BondFnL2 L →ₗ[ℝ] BondFnL2 L) := Q_surjective D
  exact ⟨(LinearMap.injective_iff_surjective (f := (D.Q : BondFnL2 L →ₗ[ℝ] BondFnL2 L))).mpr hsurj,
    hsurj⟩

#print axioms Q_surjective
#print axioms collapsed_Q_bijective

/-! ## §8 — NON-VACUITY AT THE TRUE BOND CARRIER

The campaign's own history makes this mandatory: a conditional theorem whose hypotheses nothing can
meet proves nothing (`compute/hleftc_decision/`).  Everything below is at
`H = K = BondFnL2 L` — **the collapse, used deliberately and only here** (§7), so that the six
ingredients can be computed in closed form.  `Q := I` here is NOT Bałaban's block average; its only
job is to inhabit the hypothesis package. -/

/-- `G₁` at the bond carrier, from the REAL construction `CovarianceG1.gOneOfNeumann`, at
`G₀ := I`, `P := (1/2)I`.  Its value `2·I` is NOT the identity, so the Neumann inversion does real
work here. -/
theorem bondGstar_eq :
    gOneOfNeumann (1 : BondFnL2 L →L[ℝ] BondFnL2 L) ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      = (2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) := by
  have h1 : ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      * ((2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) = 1 := by ext x; simp
  have h2 : ((2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      * ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) = 1 := by ext x; simp
  have hu : ((Units.mk ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      ((2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) h1 h2 : (BondFnL2 L →L[ℝ] BondFnL2 L)ˣ) :
      BondFnL2 L →L[ℝ] BondFnL2 L) = (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) := rfl
  have hinv : Ring.inverse ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      = (2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) := by
    rw [← hu, Ring.inverse_unit]; rfl
  unfold gOneOfNeumann
  have hPG : ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
      * (1 : BondFnL2 L →L[ℝ] BondFnL2 L) = (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) := by
    ext x; simp
  have hsub : (1 : BondFnL2 L →L[ℝ] BondFnL2 L) - (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
      = (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) := by
    ext x; simp; ring
  rw [hPG, hsub, hinv, one_mul]

/-- **THE WITNESS DATUM at the TRUE bond carrier**, with `Gstar` literally
`gOneOfNeumann I ((1/2)I)`. -/
noncomputable def bondData : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L) where
  Ginv := (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
  Gstar := gOneOfNeumann (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
    ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
  Ginv_Gstar := by intro x; rw [bondGstar_eq]; show (1/2 : ℝ) • ((2 : ℝ) • x) = x; rw [smul_smul]; norm_num
  Gstar_Ginv := by intro x; rw [bondGstar_eq]; show (2 : ℝ) • ((1/2 : ℝ) • x) = x; rw [smul_smul]; norm_num
  Ginv_selfAdjoint := by
    intro x y
    show (inner ℝ ((1/2 : ℝ) • x) y : ℝ) = inner ℝ x ((1/2 : ℝ) • y)
    rw [real_inner_smul_left, real_inner_smul_right]
  Ginv_posSemidef := by
    intro x
    show (0 : ℝ) ≤ inner ℝ x ((1/2 : ℝ) • x)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    positivity
  Q := 1
  Qstar := 1
  Q_Qstar_adjoint := by intro x y; rfl
  Comp := (2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
  Comp_eq := by
    intro x
    rw [bondGstar_eq]
    show (2 : ℝ) • x = (2 : ℝ) • x
    rfl
  CompInv := (1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
  Comp_CompInv := by intro x; show (2 : ℝ) • ((1/2 : ℝ) • x) = x; rw [smul_smul]; norm_num
  CompInv_Comp := by intro x; show (1/2 : ℝ) • ((2 : ℝ) • x) = x; rw [smul_smul]; norm_num

/-- `H₁ = G₁Q*(QG₁Q*)⁻¹ = I` at the witness datum, computed. -/
theorem bondData_H1 (x : BondFnL2 L) : solutionOperator (bondData (L := L)) x = x := by
  rw [solutionOperator_apply]
  show (bondData (L := L)).Gstar ((1 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) x)) = x
  show (bondData (L := L)).Gstar ((1/2 : ℝ) • x) = x
  show gOneOfNeumann (1 : BondFnL2 L →L[ℝ] BondFnL2 L)
    ((1/2 : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) ((1/2 : ℝ) • x) = x
  rw [bondGstar_eq]
  show (2 : ℝ) • ((1/2 : ℝ) • x) = x
  rw [smul_smul]; norm_num

/-- **A GENUINELY QUADRATIC `Qext`**, matching CMP99b p.427's description of `D̃⁽²⁾` as *a quadratic
polynomial in `B`*.  Disclosed stand-in: NOT CMP99b's own `Q_j` (blocked on the unformalized `Ū^j`
of [5]/CMP98, `DeltaKAssembly` §0 finding 2). -/
noncomputable def bondQext (v : BondFnL2 L) : BondFnL2 L → BondFnL2 L := fun x => ‖x‖ ^ 2 • v

/-- `D̃⁽²⁾(B) = ‖B‖²·v` — `SourceJ.Dtilde2Shape`'s real second-derivative extraction, COMPUTED. -/
theorem bondDtilde2 (v B : BondFnL2 L) : Dtilde2Shape (bondQext v) B = ‖B‖ ^ 2 • v := by
  show taylorQuadraticTerm (fun t : ℝ => ‖t • B‖ ^ 2 • v) = ‖B‖ ^ 2 • v
  have h : (fun t : ℝ => ‖t • B‖ ^ 2 • v) = fun t : ℝ => t ^ 2 • (‖B‖ ^ 2 • v) := by
    funext t
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, smul_smul]
  rw [h, taylorQuadraticTerm_sq_smul]

/-- The source term at the witness, in closed form: `⟨H₁D̃⁽²⁾(B),J⟩ = ‖B‖²·⟨v,J⟩`. -/
theorem bondData_sourceTerm (v J B : BondFnL2 L) :
    sourceTerm (bondData (L := L)) (bondQext v) J B = ‖B‖ ^ 2 * (inner ℝ v J : ℝ) := by
  show (inner ℝ (solutionOperator (bondData (L := L)) (Dtilde2Shape (bondQext v) B)) J : ℝ) = _
  rw [bondDtilde2, bondData_H1, real_inner_smul_left]

/-- **THE NAMED RESIDUAL IS DISCHARGED AT THIS INSTANCE** — `IsSourceOperator` is inhabited, with
`S = ⟨v,J⟩·I`.  The hypothesis package of §3/§5 is therefore not empty. -/
theorem bondData_isSourceOperator (v J : BondFnL2 L) :
    IsSourceOperator (bondData (L := L)) (bondQext v) J
      ((inner ℝ v J : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L)) := by
  intro B
  rw [bondData_sourceTerm]
  show (inner ℝ B ((inner ℝ v J : ℝ) • B) : ℝ) = _
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- **THE COMPRESSED PRINTED FORM AT THE WITNESS, IN CLOSED FORM.**  All three printed summands are
present: `1/2` is `⟨B,(QG₁Q*)⁻¹B⟩`'s coefficient, `a` is the (3.156) constant, `2⟨v,J⟩` is the
source term's. -/
theorem bondData_cdcFormTrue (bc : BaseConstant) (v J : BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) :
    cdcFormTrue (bondData (L := L)) bc (bondQext v) J U ell Dinv w
      = ((1/2 : ℝ) - usedAt bc 0 - 2 * (inner ℝ v J : ℝ)) * ‖cZero U ell Dinv w‖ ^ 2 := by
  show deltaKForm (bondData (L := L)) bc (bondQext v) J (cZero U ell Dinv w) = _
  rw [deltaKForm_split, bondData_sourceTerm]
  have hC : (inner ℝ (cZero U ell Dinv w) ((bondData (L := L)).CompInv (cZero U ell Dinv w)) : ℝ)
      = (1/2 : ℝ) * ‖cZero U ell Dinv w‖ ^ 2 := by
    show (inner ℝ (cZero U ell Dinv w) ((1/2 : ℝ) • (cZero U ell Dinv w)) : ℝ) = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hC, real_inner_self_eq_norm_sq]
  ring

/-- `‖C₀B̃‖ > 0` for `B̃ ≠ 0` — from `construct_cdc`'s injectivity of `C₀`. -/
theorem norm_cZero_pos (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < ‖cZero U ell Dinv w‖ := by
  refine norm_pos_iff.mpr ?_
  intro h
  exact hw (cZero_injective U ell Dinv (by rw [h, map_zero]))

/-- **THE PRINTED SUBSPACE DOES NOT KILL THE SOURCE TERM.**  At the true bond carrier, at
`construct_cdc`'s own named nonzero element of `ℓ²(Λ̃)`, the source term is nonzero whenever
`⟨v,J⟩ ≠ 0`.  This is the fact that makes §6's failure theorem non-vacuous. -/
theorem sourceTerm_ne_zero_on_printed_subspace {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (v J : BondFnL2 L)
    (hvJ : (inner ℝ v J : ℝ) ≠ 0) :
    sourceTerm (bondData (L := L)) (bondQext v) J
        (cZero U ell Dinv (tildeSpike hell2 hdvd)) ≠ 0 := by
  rw [bondData_sourceTerm]
  have hpos := norm_cZero_pos U Dinv (tildeSpike (L := L) hell2 hdvd) (tildeSpike_ne_zero hell2 hdvd)
  exact mul_ne_zero (by positivity) hvJ

/-- **`D̃⁽²⁾` IS NONZERO ON THE PARAMETRISED PRINTED SUBSPACE** at the witness — the hypothesis
`printed_cdc_not_posDef_general` consumes, discharged at a concrete instance so that the
general statement is not conditional on something nothing meets. -/
theorem bondDtilde2_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (v : BondFnL2 L) (hv : v ≠ 0) :
    Dtilde2Shape (bondQext v) (cZero U ell Dinv (tildeSpike hell2 hdvd)) ≠ 0 := by
  rw [bondDtilde2]
  have hpos := norm_cZero_pos U Dinv (tildeSpike (L := L) hell2 hdvd)
    (tildeSpike_ne_zero hell2 hdvd)
  exact smul_ne_zero (by positivity) hv

/-- **THE GENERAL FAILURE THEOREM IS NON-VACUOUS**: `printed_cdc_not_posDef_general`'s hypotheses
are met at a concrete datum, a concrete `Qext`, and `construct_cdc`'s own named nonzero element of
`ℓ²(Λ̃)`. -/
theorem printed_cdc_not_posDef_general_at_witness (bc : BaseConstant) {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (v : BondFnL2 L) (hv : v ≠ 0) :
    ∃ J : BondFnL2 L, ¬ (∀ w : TildeFn L ell, w ≠ 0 →
      (0 : ℝ) < cdcFormTrue (bondData (L := L)) bc (bondQext v) J U ell Dinv w) :=
  printed_cdc_not_posDef_general (bondData (L := L)) bc (bondQext v) U Dinv
    (tildeSpike hell2 hdvd) (tildeSpike_ne_zero hell2 hdvd)
    (bondDtilde2_ne_zero hell2 hdvd U Dinv v hv)

#print axioms bondDtilde2_ne_zero
#print axioms printed_cdc_not_posDef_general_at_witness

#print axioms bondGstar_eq
#print axioms bondData
#print axioms bondData_H1
#print axioms bondQext
#print axioms bondDtilde2
#print axioms bondData_sourceTerm
#print axioms bondData_isSourceOperator
#print axioms bondData_cdcFormTrue
#print axioms norm_cZero_pos
#print axioms sourceTerm_ne_zero_on_printed_subspace

/-! ## §9 — THE CONTRAST, IN ONE INSTANCE: POSITIVE DEFINITE AT `J = 0`, NEGATIVE AT A COMPUTED `J`

The `(QG₁Q*)⁻¹` summand and the `a` summand are IDENTICAL in the two halves.  Only `J` moves. -/

/-- Positive definite when the composite coefficient is positive — in particular at `J = 0`
whenever `a < 1/2`. -/
theorem bondData_posDef_of_coeff (bc : BaseConstant) (v J : BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hcoef : 0 < (1/2 : ℝ) - usedAt bc 0 - 2 * (inner ℝ v J : ℝ))
    (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) J U ell Dinv w := by
  rw [bondData_cdcFormTrue]
  have hpos := norm_cZero_pos U Dinv w hw
  positivity

/-- **THE FLIP.**  One instance at the true bond carrier: positive definite at `J = 0` (given
`a < 1/2`), and STRICTLY NEGATIVE at an explicitly computed `J = lam·v`, at `construct_cdc`'s own
named nonzero element of `ℓ²(Λ̃)`.  Nothing but `J` differs between the two conclusions. -/
theorem bondData_posDef_flips_with_J (bc : BaseConstant) {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (ha : usedAt bc 0 < 1/2) (v : BondFnL2 L) (hv : v ≠ 0) :
    (∀ w : TildeFn L ell, w ≠ 0 →
        0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) (0 : BondFnL2 L) U ell Dinv w)
      ∧ (0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) (0 : BondFnL2 L) U ell Dinv
          (tildeSpike hell2 hdvd))
      ∧ ∃ lam : ℝ, cdcFormTrue (bondData (L := L)) bc (bondQext v) (lam • v) U ell Dinv
          (tildeSpike hell2 hdvd) < 0 := by
  have hvn : (0 : ℝ) < ‖v‖ ^ 2 := by
    have : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hzero : ∀ w : TildeFn L ell, w ≠ 0 →
      0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) (0 : BondFnL2 L) U ell Dinv w := by
    intro w hw
    refine bondData_posDef_of_coeff bc v 0 U Dinv ?_ w hw
    rw [inner_zero_right]
    linarith
  refine ⟨hzero, hzero _ (tildeSpike_ne_zero hell2 hdvd), ?_⟩
  · refine ⟨((1/2 : ℝ) - usedAt bc 0 + 1) / (2 * ‖v‖ ^ 2), ?_⟩
    rw [bondData_cdcFormTrue]
    have hinner : (inner ℝ v ((((1/2 : ℝ) - usedAt bc 0 + 1) / (2 * ‖v‖ ^ 2)) • v) : ℝ)
        = (((1/2 : ℝ) - usedAt bc 0 + 1) / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hinner]
    have hcoef : (1/2 : ℝ) - usedAt bc 0
        - 2 * ((((1/2 : ℝ) - usedAt bc 0 + 1) / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2) = -1 := by
      field_simp
      ring
    rw [hcoef]
    have hpos := norm_cZero_pos U Dinv (tildeSpike (L := L) hell2 hdvd)
      (tildeSpike_ne_zero hell2 hdvd)
    nlinarith [hpos]

#print axioms bondData_posDef_of_coeff
#print axioms bondData_posDef_flips_with_J

/-! ## §10 — THE CLOSING STATEMENT, AS ONE DECLARATION

Everything the dispatch asked for, in a single theorem: the printed subspace's two non-vacuous
clauses hold at `C₀B̃`; the printed three-term `Δ_k` is an operator; `construct_cdc`'s `cdcOp` at
the pinned `T2` has the printed (3.156) form as its quadratic form; and the pin is unique. -/

theorem printed_cdc_closing_statement (D : BalabanCovarianceData H (BondFnL2 L))
    (bc : BaseConstant) (Qext : BondFnL2 L → BondFnL2 L) (J : H)
    (S : BondFnL2 L →L[ℝ] BondFnL2 L) (hS : IsSourceOperator D Qext J S)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (w : TildeFn L ell) :
    ((∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell
        (fun b => (cZero U ell (dinvC U ell) w : BondFnL2 L) b) c = 0)
      ∧ (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
          ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
          ∀ e ∈ staircasePath y' x, (cZero U ell (dinvC U ell) w : BondFnL2 L) e = 0))
    ∧ (∀ B : BondFnL2 L, (inner ℝ B (printedDeltaKOp D bc S B) : ℝ) = deltaKForm D bc Qext J B)
    ∧ (inner ℝ w (cdcOp U ell (dinvC U ell) (pinnedT2 D bc S U) w) : ℝ)
        = cdcFormTrue D bc Qext J U ell (dinvC U ell) w
    ∧ (∀ T2 : BondFnL2 L →L[ℝ] BondFnL2 L,
        (∀ x : BondFnL2 L, deltaK U T2 x = printedDeltaKOp D bc S x) ↔ T2 = pinnedT2 D bc S U) :=
  ⟨cZero_in_printed_subspace hell hdvd U w,
   fun B => inner_printedDeltaKOp D bc Qext J S hS B,
   inner_cdcOp_pinnedT2 D bc Qext J S hS U ell (dinvC U ell) w,
   fun T2 => pinnedT2_unique D bc S U T2⟩

#print axioms printed_cdc_closing_statement

end AdalyFormal.Balaban.DeltaKWiring
