/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKUnified
import AdalyFormal.Balaban.RegularityHolonomy
import R7Fork.AdalyFormal.Balaban.RegularUCoercivity
import AdalyFormal.Balaban.Coercivity
import R7Fork.AdalyFormal.Balaban.NonFlatBackground

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
⚠⚠ **`UconfigReg` WAS THE FLAT SET — RE-INDEXED 2026-07-26 (§4, `compute/uconfigreg_reindex/`).**
`UconfigReg` was `{U // IsRegularHolonomy U 0}` and was described throughout this file as "the
regular-`U` SUBTYPE ... CMP99b p.428's own TRUE deferred claim". `NonFlatBackground.
isRegularHolonomy_zero_iff_flat` proves `IsRegularHolonomy U 0 ↔ ∀ p, holonomyElem U p = 1`, so
**at threshold `0` the "regular" set is EXACTLY the flat-holonomy set** and every statement
quantified over `UconfigReg` was a statement about flat backgrounds — i.e. about `U = 1` up to
gauge, precisely the case CMP96 [4] Lemma 2.4 ALREADY proves and which p.428 explicitly says is
*not* the open part. Re-proved in this file as `UconfigReg_all_flat` /
`no_curved_mem_UconfigReg`, so the defect is a matter of record rather than of prose.

**WHY THE EXISTING NON-DEGENERACY CONTROL DID NOT CATCH IT (the lesson, kept deliberately).**
`instance : Nontrivial UconfigReg` PASSES: `uReg0 = trivialU` and `uReg1 = pureGaugeU` really are
distinct terms (`uReg0_ne_uReg1`). But `Nontrivial` only says *two elements differ*; it cannot say
that the subtype contains an element the DISCRIMINATING property separates from the degenerate
ones. Both witnesses sat at the degenerate point: `NonFlatBackground.pureGaugeU_holonomy_eq_one`
proves `pureGaugeU` is FLAT (it was labelled "GENUINELY NON-FLAT" in this tree until 2026-07-26),
and the only thing `pureGaugeU_ne_trivial` ever established is that ONE BARE LINK VALUE differs
from `1` — a gauge-VARIANT fact with no field-strength content. A green `Nontrivial` over a
degenerate domain is the exact shape of a control that cannot fail. The replacement control is
`exists_curved_mem_UconfigRegPos` (§4b): it demands an inhabitant with `holonomyElem ≠ 1` at some
plaquette AND that is not the gauge transform of ANY flat configuration.

**THE RE-INDEX (§4).** `UconfigRegPos (α : ℝ) := {U // IsRegularHolonomy U α}`, with
`UconfigReg` retained as `UconfigRegPos 0` — DEFINITIONALLY the old subtype, so no existing
statement changes meaning. See §4's own docstrings for what survived re-targeting (§10b: all of
it — nothing in the construction used flatness) and for the finding that the regularity
restriction is INERT for THIS `Δ`.
-/

/-!
⚠ **`gamma_exists_su2` CONVICTED FALSE-AS-TYPED (prosecutor 2026-07-23,
`compute/prosecute_su2_build/`).** The operator on `V` reduces EXACTLY to `scalar(U)·‖v‖²`,
`scalar(U) = (baseG+κ(U))⁻¹ − bc.a − 2⟪v0,J⟫` (scalarization CONFIRMED, zero residual operator
content). `bc.a` is a FREE argument (only `a>0`), so `bc.a:=2` makes the scalar negative for every
regular `U` → no `γ>0` exists (compiled counterexample). FIX: pin one global `bc` / bound `bc.a`
against `κ`'s bound (a dropped-hypothesis repair). DEEPER: even fixed, the sorry is a SCALAR proxy,
not Bałaban's real `Δ_k(U)` — the faithful operator needs `[LEM-Q1REAL-ADJOINT]` (promote `Q₁(U)`
into the real `Q`/`Qstar`, not the scalar `κ` route). The STRUCTURE below (su(2) carrier, real `Ad(U)`
`U`-dependence, defects a/b/c fixed, faithful subspace) is a genuine advance and retained; the
OPERATOR CONTENT is not yet faithful. NOT wired.

# `C*Δ_kC`, faithfully assembled over the REAL `su(2)` carrier — FULL su(2) RE-CARRY

**Dispatch target** (owner order, "proceed with the su(2) re-carry, to its fullest extent"):
replace `FaithfulCoercivity.lean` (CONVICTED, `compute/prosecute_faithful_stage1/VERDICT.md`) —
built over the SCALAR `Balaban.Anchoring.AnchoredBondSpace Lat = EuclideanSpace ℝ (Bond Lat)`,
which cannot host genuine `U`-dependence, forcing `Δ_nonconstant` to be an ASSUMED field — with
a build over the real `su(2)`-valued carrier `Bond L → SuTwo`, where `Q₁(U)` acts by the adjoint
`Ad(U)` and genuine `U`-dependence is REAL, not faked.

## THE LOAD-BEARING FINDING OF THIS DISPATCH (read before anything else)

`Balaban.DeltaKUnified.lean` ALREADY built (3.156)/(3.157)'s carrier — `BFL2 witnessL :=
WithLp 2 (Bond witnessL → SuTwo)` — and CMP96 (2.121)'s admissible subspace on it
(`subspace156BFL2`, whose `Q₁`-clause is `Q1Real.q1RealKernel U`, the REAL per-bond, per-path
transport `Q1Real.lean` builds — CMP96 (2.121) faithfully, over the `su(2)` carrier). **But**
`deltaKUnifiedData.Q := 1`, `.Qstar := 1` (the literal identity) — a disclosed simplification
that leaves `Δ_k`'s OPERATOR VALUE entirely `U`-independent; `U` enters ONLY through which `B`
are admissible (the subspace membership condition), never through `Δ_k(U)`'s own action.
`Balaban.RegularUCoercivity.lean` already PROVES this defect explicitly
(`deltaKFormOnSubspace156_U_independent`, general in `U`) and shows the naive coercivity bound
is FALSE for free `Qext`/`J` even restricted to `trivialU`-regular backgrounds. **This is the
precise, measured form of the mandate's "scalar carrier cannot host `U`-dependence" diagnosis —
except it recurs even on the correct `su(2)` carrier, because the PRIOR wiring never threaded
`Q1Real(U)`'s genuine variation into the operator, only into the domain.** This file's
deliverable is exactly that missing thread: `Q₁(U)`'s combinatorial variation (`Q1Real.lean`,
already `#print axioms`-clean, no `sorry`) is made to drive `Gstar(U)`/`Ginv(U)` (hence
`CompInv(U)`, hence `Δ_k(U)`'s value) genuinely, provably.

## THE CONSTRUCTION: `κ(U)`, a bounded, real, PROVABLY-`U`-dependent scalar built from `Q1Real`

`κ(U) := ⟪Q1Real U d4ConfigSuTwo targetCoarseBond, suTwoWitness⟫` — the real number obtained by
pairing `Q1Real`'s already-computed value at its own non-degenerate witness (`Q1Real.lean` §7,
`d4ConfigSuTwo`/`targetCoarseBond`) against the fixed direction `suTwoWitness`. Closed form
(`kappa_eq`, derived from `Q1Real.q1RealMain_d4ConfigSuTwo`, itself `sorry`-free): `κ(U) =
(1/4)⟪RMap(U(witnessY,0)) suTwoWitness, suTwoWitness⟫` — LITERALLY Bałaban's adjoint transport
`Ad(U)` (`RMap`, `CovariantOperators.lean`) applied to a fixed Lie-algebra direction, paired with
itself. **`RMap` is ALREADY PROVED an isometry w.r.t. `SuTwoInner`'s inner product**
(`SuTwoInner.inner_RMap`, pre-existing, not built here) — this is what makes `κ` UNIFORMLY
bounded (`kappa_bound`, Cauchy–Schwarz + the isometry), which is what makes `Gstar(U) :=
(baseG+κ(U))•id` INVERTIBLE FOR EVERY `U`, unconditionally, by a single fixed choice of `baseG`.

`Gstar(U)`/`Ginv(U)` are scalar multiples of `id` (mirroring `DeltaKUnified.deltaKUnifiedData`'s
OWN established `GstarBFL2 := 2•1`/`GinvBFL2 := (1/2)•1` pattern — the SAME shape, with the
constant `2` now REPLACED by the genuinely `U`-dependent `baseG+κ(U)`). `Q := Qstar := 1` is
KEPT (the `H=K` disclosed collapse `DeltaKUnified.lean` already carries, unchanged here — not a
new simplification this file introduces).

## THE THREE CONVICTED DEFECTS, FIXED (stage-1's own findings, `VERDICT.md`)

(a) **`coercive` was FALSE-AS-TYPED, `γ0` free.** FIX: `Uconfig` is restricted to the SUBTYPE
`{U // RegularityHolonomy.IsRegularHolonomy U 0}` (Bałaban's own (3.35)/(3.36)-style regularity,
ALREADY built and validated in `RegularityHolonomy.lean`, reused verbatim) — `coercive`'s type,
`∀ (k:ℕ) (U:Uconfig), ...`, now STRUCTURALLY only ranges over regular `U`, matching CMP99b
p.428's own TRUE deferred claim ("we can prove it ... with an arbitrary configuration `U`
satisfying (3.35),(3.36)"). AND `γ''` is no longer a caller-supplied free parameter: it is bound
via `Classical.choose` from ONE existential `sorry` (`gamma_exists_su2`), so the stage-1 exploit
(`γ0 := ‖Δ‖+1`, chosen AFTER seeing `Δ`) is not even EXPRESSIBLE against this signature — there
is no such argument to supply it through.
(b) **`hSourceCorrection` was vacuous at `J=0`.** FIX: `J ≠ 0` is an EXPLICIT hypothesis of the
constructor (`hJ`), and `sourceCorrection` is built CONCRETELY (not a free field satisfying only
an equality `0` trivially discharges): `Qext := RegularUCoercivity.qextQuad v0` (LAW-19 reuse),
so `Dtilde2Shape Qext v = ‖v‖²•v0` (already proved, `dtilde2_qextQuad`), and
`sourceCorrection := c•id` with `c := -2⟪solutionOperator(cov U) v0, J⟫` — CLOSED FORM, and
`⟪v,sourceCorrection v⟫ = c‖v‖² = -2⟪H₁(D̃²(Qext,v)),J⟫` EXACTLY (proved, `hSourceCorrection_eq`),
not merely typed.
(c) **`C` was collapsible to `id`.** FIX: `ReparamDataSU2` requires (i) `C`'s image lies in the
ADMISSIBLE subspace `subspace156BFL2` (proper, `≠⊤`, for EVERY `U` — `subspace156_ne_top`, from
`Q1Real.q1RealKernel_ne_top`, itself unconditional in `U`) and (ii) `C` is the IDENTITY on that
subspace (a genuine retraction). `C := id` satisfies (i) ONLY if the subspace is `⊤` — which it
provably is NOT — so `id` is STRUCTURALLY EXCLUDED, not merely shown to break the bound.

## WHAT IS EXPLICITLY INHERITED, NOT A NEW DEFECT OF THIS FILE

`Lat := witnessL` fixed (`Q1Real`/`subspace156BFL2` are both only built at `witnessL`/`witnessEll`
in this tree — the SAME restriction `DeltaKUnified.lean`/`Q1Real.lean` already carry). `H=K`
(Fine=Coarse) collapsed onto ONE carrier `BFL2 witnessL` (`DeltaKUnified.lean`'s own disclosed
simplification). `Q := Qstar := 1` (same file, same disclosure) — consequently `H₁ = solutionOperator
(su2CovarianceData U) = id` UNCONDITIONALLY (`solutionOperator_su2_eq_id`, mirroring
`RegularUCoercivity.solutionOperator_deltaKUnifiedData_eq_id`'s identical mechanism), which is
WHY `sourceCorrection`'s scalar `c` ends up `U`-INDEPENDENT here — a disclosed CONSEQUENCE of the
inherited `Q:=1` simplification, not a new defect: the genuine `U`-dependence this file adds
lives entirely in `Gstar(U)`/`Ginv(U)`/`CompInv(U)`, the FIRST term of (3.156), which is now
real.

## NAMED, NOT BUILT

`Q1Real` itself is fixed to `witnessL`/`witnessEll` (a Lat-generic version is a comparable-size
undertaking — `BondSU2Space.lean` §6's own residual note, unchanged here). The FULL general
adjoint of `Q1Real(U)` (needed to promote `Q1Real(U)` itself into the `Q`/`Qstar` slots of
`BalabanCovarianceData`, rather than routing its variation through the SCALAR `κ(U)`) is NOT
built — it would require transposing `q1RealMain`'s nested `(x,i)`-indexed `Finset.sum` (a
genuine gather/scatter Fubini argument), comparable in scope to `Q1Real.lean` itself. Tagged
`[LEM-Q1REAL-ADJOINT]`. This file's `κ(U)` route achieves the mandate's actual goal (`Δ_k(U)`'s
VALUE genuinely, provably `U`-dependent, DERIVED from `Q1Real`, not assumed) WITHOUT needing that
adjoint — a smaller, sufficient construction, not a proxy for it (the scalar IS `Q1Real(U)`'s own
output, paired against a fixed direction, not an invented stand-in).
-/

namespace AdalyFormal.Balaban.FaithfulCoercivitySU2

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration PeriodicLatticePlaquette periodicGaugeTransform)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.NonFlatBackground (nonflatU nonflatU_at_x_mu nonflatU_isRegularHolonomy
  nonflatU_curvature_ne_one nonflatU_has_curved_plaquette nonflatU_not_gaugeTransform_of_flat
  exists_curved_regular_below isRegularHolonomy_zero_iff_flat rotElem rotElem_coe rotA rotB
  rotA_sq_add_rotB_sq frobSupBond_nonflatU pureGaugeU_holonomy_eq_one)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero
  suTwoWitnessVal RMap RMap_coe_apply RMap_one RMap_witnessMElem witnessU witnessU_at_x_mu
  witnessPlaquette)
open AdalyFormal.Balaban.SuTwoInner (inner_RMap)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv subspace156BFL2 subspace156BFL2_ne_bot)
open AdalyFormal.Balaban.Q1Real (q1RealMain_d4ConfigSuTwo d4ConfigSuTwo
  q1RealKernel q1RealKernel_ne_top checkerConfigSuTwo)
open AdalyFormal.Balaban.QOne (targetCoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularityHolonomy (IsRegularHolonomy trivialU_isRegularHolonomy
  pureGaugeU pureGaugeU_isRegularHolonomy_zero pureGaugeU_at_x_mu pureGaugeU_ne_trivial)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.RegularUCoercivity (qextQuad dtilde2_qextQuad)

/-! ## §1 — `κ(U)`, the genuine `Q1Real`-driven scalar, and its uniform bound -/

/-- **`κ(U)`, LITERALLY built from `Q1Real U`** — the real number obtained by pairing `Q1Real`'s
own already-computed value on its own non-degenerate witness (`d4ConfigSuTwo`/`targetCoarseBond`,
`Q1Real.lean` §7) against the fixed direction `suTwoWitness`. -/
noncomputable def kappa
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) : ℝ :=
  (inner ℝ (AdalyFormal.Balaban.Q1Real.Q1Real U d4ConfigSuTwo targetCoarseBond) suTwoWitness : ℝ)

/-- **Closed form**, derived (not assumed) from `Q1Real.q1RealMain_d4ConfigSuTwo` (itself
`sorry`-free): `κ(U) = (1/4)⟪RMap(U(witnessY,0)) suTwoWitness, suTwoWitness⟫` — Bałaban's own
adjoint transport `Ad(U)`, applied to a fixed direction. -/
theorem kappa_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    kappa U = (1 / 4 : ℝ) *
      (inner ℝ (RMap (U (witnessY, (0 : Fin 3))) suTwoWitness) suTwoWitness : ℝ) := by
  unfold kappa
  rw [AdalyFormal.Balaban.Q1Real.Q1Real_apply, q1RealMain_d4ConfigSuTwo, real_inner_smul_left]

/-- **`RMap` preserves norms** — a direct corollary of `SuTwoInner.inner_RMap` (`RMap` is
ALREADY proved an isometry there; this file derives the norm-level statement it needs). -/
theorem norm_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap g X‖ = ‖X‖ := by
  have h : (inner ℝ (RMap g X) (RMap g X) : ℝ) = inner ℝ X X := inner_RMap g X X
  have h1 : ‖RMap g X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]; exact h
  have hsq := congrArg Real.sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsq

/-- **THE UNIFORM BOUND**: `|κ(U)| ≤ ‖suTwoWitness‖²`, for EVERY `U` — Cauchy–Schwarz
(`abs_real_inner_le_norm`) plus `RMap`'s isometry (`norm_RMap`). This is what makes a SINGLE
`baseG` invert `baseG+κ(U)` for every `U` at once, unconditionally. -/
theorem kappa_bound
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    |kappa U| ≤ ‖(suTwoWitness : SuTwo)‖ ^ 2 := by
  rw [kappa_eq]
  have hcs := abs_real_inner_le_norm
    (RMap (U (witnessY, (0 : Fin 3))) suTwoWitness) (suTwoWitness : SuTwo)
  rw [norm_RMap] at hcs
  calc |(1 / 4 : ℝ) * (inner ℝ (RMap (U (witnessY, (0 : Fin 3))) suTwoWitness) suTwoWitness : ℝ)|
      = (1 / 4 : ℝ) *
        |(inner ℝ (RMap (U (witnessY, (0 : Fin 3))) suTwoWitness) suTwoWitness : ℝ)| := by
        rw [abs_mul]; norm_num
    _ ≤ (1 / 4 : ℝ) * (‖(suTwoWitness : SuTwo)‖ * ‖(suTwoWitness : SuTwo)‖) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ ‖(suTwoWitness : SuTwo)‖ ^ 2 := by rw [sq]; nlinarith [norm_nonneg (suTwoWitness : SuTwo)]

#print axioms kappa_eq
#print axioms norm_RMap
#print axioms kappa_bound

/-! ## §2 — `Gstar(U)`/`Ginv(U)`: genuine scalar-multiple-of-`id` operators, `U`-dependent via
`κ`, invertible for EVERY `U` by a single fixed choice of `baseG` -/

/-- `baseG := ‖suTwoWitness‖²+1` — chosen so `baseG+κ(U) ≥ 1 > 0` for every `U`
(`kappa_bound`). -/
noncomputable def baseG : ℝ := ‖(suTwoWitness : SuTwo)‖ ^ 2 + 1

theorem baseG_add_kappa_pos
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (1 : ℝ) ≤ baseG + kappa U := by
  have h := kappa_bound U
  rw [abs_le] at h
  unfold baseG
  linarith [h.1]

theorem baseG_add_kappa_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    baseG + kappa U ≠ 0 := by
  have := baseG_add_kappa_pos U; linarith

/-- **`Gstar(U)`, genuinely `U`-dependent** — the SAME scalar-multiple-of-`id` shape
`DeltaKUnified.GstarBFL2 := 2•1` already carries, with the constant `2` replaced by
`baseG+κ(U)`. -/
noncomputable def GstarSU2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (baseG + kappa U) • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)

noncomputable def GinvSU2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (baseG + kappa U)⁻¹ • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)

theorem GinvSU2_GstarSU2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (x : BFL2 witnessL) : GinvSU2 U (GstarSU2 U x) = x := by
  unfold GinvSU2 GstarSU2
  show (baseG + kappa U)⁻¹ • ((baseG + kappa U) • x) = x
  rw [smul_smul, inv_mul_cancel₀ (baseG_add_kappa_ne_zero U), one_smul]

theorem GstarSU2_GinvSU2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (x : BFL2 witnessL) : GstarSU2 U (GinvSU2 U x) = x := by
  unfold GinvSU2 GstarSU2
  show (baseG + kappa U) • ((baseG + kappa U)⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ (baseG_add_kappa_ne_zero U), one_smul]

theorem GinvSU2_selfAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (x y : BFL2 witnessL) :
    (inner ℝ (GinvSU2 U x) y : ℝ) = inner ℝ x (GinvSU2 U y) := by
  unfold GinvSU2
  show (inner ℝ ((baseG + kappa U)⁻¹ • x) y : ℝ) = inner ℝ x ((baseG + kappa U)⁻¹ • y)
  rw [real_inner_smul_left, real_inner_smul_right]

theorem GinvSU2_posSemidef
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (x : BFL2 witnessL) : (0 : ℝ) ≤ inner ℝ x (GinvSU2 U x) := by
  unfold GinvSU2
  show (0 : ℝ) ≤ inner ℝ x ((baseG + kappa U)⁻¹ • x)
  rw [real_inner_smul_right]
  have hpos := baseG_add_kappa_pos U
  have hinv : (0:ℝ) ≤ (baseG + kappa U)⁻¹ := by positivity
  have hnn : (0:ℝ) ≤ (inner ℝ x x : ℝ) := real_inner_self_nonneg
  exact mul_nonneg hinv hnn

#print axioms baseG_add_kappa_pos
#print axioms baseG_add_kappa_ne_zero
#print axioms GinvSU2_GstarSU2
#print axioms GstarSU2_GinvSU2
#print axioms GinvSU2_selfAdjoint
#print axioms GinvSU2_posSemidef

/-- **THE WIRED `BalabanCovarianceData`, `U`-dependent** — `Gstar`/`Ginv` are the REAL,
`Q1Real`-driven scalars (§2); `Q := Qstar := 1` is the INHERITED `DeltaKUnified.lean`
simplification (module docstring), unchanged here. -/
noncomputable def su2CovarianceData
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BalabanCovarianceData (BFL2 witnessL) (BFL2 witnessL) where
  Ginv := GinvSU2 U
  Gstar := GstarSU2 U
  Ginv_Gstar := GinvSU2_GstarSU2 U
  Gstar_Ginv := GstarSU2_GinvSU2 U
  Ginv_selfAdjoint := GinvSU2_selfAdjoint U
  Ginv_posSemidef := GinvSU2_posSemidef U
  Q := 1
  Qstar := 1
  Q_Qstar_adjoint := fun _ _ => rfl
  Comp := GstarSU2 U
  Comp_eq := fun _ => rfl
  CompInv := GinvSU2 U
  Comp_CompInv := GstarSU2_GinvSU2 U
  CompInv_Comp := GinvSU2_GstarSU2 U

#print axioms su2CovarianceData

/-! ## §3 — `κ` genuinely SEPARATES two REGULAR configurations (defect (a)'s witnesses,
reused for `Δ_nonconstant`, §6) -/

theorem kappa_trivialU_pos : (0 : ℝ) < kappa (trivialU witnessL) := by
  rw [kappa_eq]
  have h0 : (trivialU witnessL) (witnessY, (0 : Fin 3)) = 1 := rfl
  rw [h0, RMap_one]
  show (0:ℝ) < (1/4:ℝ) * (inner ℝ (suTwoWitness : SuTwo) suTwoWitness : ℝ)
  rw [real_inner_self_eq_norm_sq]
  have : (0:ℝ) < ‖(suTwoWitness : SuTwo)‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  positivity

theorem kappa_pureGaugeU_neg : kappa pureGaugeU < (0 : ℝ) := by
  rw [kappa_eq, pureGaugeU_at_x_mu, RMap_witnessMElem]
  show (1/4:ℝ) * (inner ℝ (-(suTwoWitness : SuTwo)) suTwoWitness : ℝ) < 0
  rw [inner_neg_left, real_inner_self_eq_norm_sq]
  have : (0:ℝ) < ‖(suTwoWitness : SuTwo)‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  nlinarith [sq_nonneg ‖(suTwoWitness : SuTwo)‖]

theorem kappa_trivialU_ne_pureGaugeU : kappa (trivialU witnessL) ≠ kappa pureGaugeU := by
  have h1 := kappa_trivialU_pos
  have h2 := kappa_pureGaugeU_neg
  intro h; rw [h] at h1; linarith

#print axioms kappa_trivialU_pos
#print axioms kappa_pureGaugeU_neg
#print axioms kappa_trivialU_ne_pureGaugeU

/-! ### §3b — `κ` ON A GENUINELY CURVED REGULAR BACKGROUND (2026-07-26)

`kappa_trivialU_ne_pureGaugeU` separates two configurations that are BOTH FLAT
(`NonFlatBackground.pureGaugeU_holonomy_eq_one`): it is a separation of gauge representatives,
not of field strengths. This section computes `κ` on `NonFlatBackground.nonflatU t`, whose
curvature is provably nonzero for `t ≠ 0`, so that `Δ_nonconstant` can be witnessed by a
FLAT-vs-CURVED pair. Everything here is an exact closed form; no estimate is involved. -/

/-- `⟪w,w⟫ = 1` for `w = suTwoWitness = i·diag(1,−1)`: `−(1/2)·Re tr(w²) = −(1/2)·(−2)`. This
NORMALIZATION (Bałaban's `𝔰𝔲(2)` inner product as `SuTwoInner.inner_eq_trace` ships it) is what
turns the abstract bounds of §2 into the numerals `baseG = 2`, `|κ| ≤ 1`. -/
theorem inner_suTwoWitness_self : (inner ℝ (suTwoWitness : SuTwo) suTwoWitness : ℝ) = 1 := by
  rw [inner_eq_trace]
  show -(1 / 2 : ℝ) * (Matrix.trace (suTwoWitnessVal * suTwoWitnessVal)).re = 1
  norm_num [suTwoWitnessVal, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply,
    Complex.ext_iff]

theorem norm_suTwoWitness_sq : ‖(suTwoWitness : SuTwo)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]; exact inner_suTwoWitness_self

/-- `baseG = ‖w‖² + 1 = 2`. -/
theorem baseG_eq_two : baseG = 2 := by
  unfold baseG; rw [norm_suTwoWitness_sq]; norm_num

theorem kappa_trivialU_eq : kappa (trivialU witnessL) = 1 / 4 := by
  rw [kappa_eq]
  have h0 : (trivialU witnessL) (witnessY, (0 : Fin 3)) = 1 := rfl
  rw [h0, RMap_one]
  show (1 / 4 : ℝ) * (inner ℝ (suTwoWitness : SuTwo) suTwoWitness : ℝ) = 1 / 4
  rw [inner_suTwoWitness_self]; norm_num

/-- **THE CONJUGATION, IN CLOSED FORM.** `⟪Ad(rot t)·w, w⟫ = a(t)² − b(t)²`, where
`rot t = !![a,b;−b,a]` is the rational Pythagorean rotation of `NonFlatBackground` §2. Computed
entrywise from `RMap_coe_apply` and `rotM_conjTranspose`; nothing is estimated.

**OPS-3 — how this fails.** Replace `rotM_conjTranspose` by the plain transpose without the
complex conjugation and the `(0,1)`/`(1,0)` off-diagonal entries pick up the wrong sign, giving
`a²+b² = 1` (a CONSTANT — the separation below would then be false at every `t`). The check that
catches it is `kappa_nonflatU_lt_trivialU`, which would become `1/4 < 1/4`. -/
theorem inner_RMap_rotElem_suTwoWitness (t : ℝ) :
    (inner ℝ (RMap (rotElem t) suTwoWitness) suTwoWitness : ℝ) = rotA t ^ 2 - rotB t ^ 2 := by
  rw [inner_eq_trace, RMap_coe_apply, rotElem_coe,
    AdalyFormal.Balaban.NonFlatBackground.rotM_conjTranspose]
  show -(1 / 2 : ℝ) *
    (Matrix.trace ((AdalyFormal.Balaban.NonFlatBackground.rotM t * suTwoWitnessVal *
      !![((rotA t : ℝ) : ℂ), -((rotB t : ℝ) : ℂ); ((rotB t : ℝ) : ℂ), ((rotA t : ℝ) : ℂ)]) *
      suTwoWitnessVal)).re = _
  norm_num [AdalyFormal.Balaban.NonFlatBackground.rotM, suTwoWitnessVal, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, Complex.ext_iff]
  ring

/-- `κ(nonflatU t) = (a(t)² − b(t)²)/4`. At `t = 0` this is `1/4 = κ(trivialU)`, consistent with
`NonFlatBackground.nonflatU_zero_eq_trivial`. -/
theorem kappa_nonflatU (t : ℝ) : kappa (nonflatU t) = (rotA t ^ 2 - rotB t ^ 2) / 4 := by
  rw [kappa_eq, nonflatU_at_x_mu, inner_RMap_rotElem_suTwoWitness]; ring

/-- `a(t)² − b(t)² < 1` exactly when `t ≠ 0`: `((1−t²)² − 4t²) − (1+t²)² = −8t²`. -/
theorem rotA_sq_sub_rotB_sq_lt_one {t : ℝ} (ht : t ≠ 0) : rotA t ^ 2 - rotB t ^ 2 < 1 := by
  have hs : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  unfold rotA rotB
  rw [div_pow, div_pow, div_sub_div_same, div_lt_one (by positivity)]
  nlinarith

/-- **`κ` SEPARATES THE FLAT BACKGROUND FROM A CURVED ONE** — strictly, and for every `t ≠ 0`.
Unlike `kappa_trivialU_ne_pureGaugeU`, both sides here differ in CURVATURE
(`NonFlatBackground.nonflatU_curvature_ne_one`), not merely in a gauge representative.

**OPS-3 — how this fails.** At `t = 0` it is FALSE (`nonflatU 0 = trivialU`, both sides `1/4`);
`ht` is load-bearing and `rotA_sq_sub_rotB_sq_lt_one` is where it is used. -/
theorem kappa_nonflatU_lt_trivialU {t : ℝ} (ht : t ≠ 0) :
    kappa (nonflatU t) < kappa (trivialU witnessL) := by
  rw [kappa_nonflatU, kappa_trivialU_eq]
  have := rotA_sq_sub_rotB_sq_lt_one ht
  linarith

theorem kappa_nonflatU_ne_trivialU {t : ℝ} (ht : t ≠ 0) :
    kappa (nonflatU t) ≠ kappa (trivialU witnessL) := ne_of_lt (kappa_nonflatU_lt_trivialU ht)

#print axioms inner_suTwoWitness_self
#print axioms norm_suTwoWitness_sq
#print axioms baseG_eq_two
#print axioms kappa_trivialU_eq
#print axioms inner_RMap_rotElem_suTwoWitness
#print axioms kappa_nonflatU
#print axioms rotA_sq_sub_rotB_sq_lt_one
#print axioms kappa_nonflatU_lt_trivialU
#print axioms kappa_nonflatU_ne_trivialU

/-! ## §4 — `UconfigRegPos α`, the regular-`U` subtype INDEXED BY ITS THRESHOLD

**Design choice, stated (2026-07-26).** The threshold is added as an INDEX on a new abbrev
`UconfigRegPos`, and `UconfigReg` is REDEFINED as `UconfigRegPos 0` rather than deleted. The
alternative — adding a parameter to `UconfigReg` itself — would have silently changed the meaning
of every downstream occurrence of the name. As written, `UconfigReg` is DEFINITIONALLY the old
subtype (`abbrev`s are reducible, `UconfigRegPos 0` unfolds to
`{U // IsRegularHolonomy U (0:ℝ)}`), so every pre-existing statement about it means exactly what
it meant before — it is only now labelled correctly. -/

/-- **`UconfigRegPos α := {U // IsRegularHolonomy U α}`** — Bałaban's regular-`U` restriction
(`RegularityHolonomy.lean`, reused verbatim, LAW-19) at an EXPLICIT threshold `Mα₀ := α`. CMP99b
p.428's deferred claim is asked "with an arbitrary configuration `U` satisfying (3.35),(3.36)
with `Mα₀` **sufficiently small**" — *small*, and in particular POSITIVE; at `α = 0` the
condition degenerates to flatness (`isRegularHolonomy_zero_iff_flat`) and the claim collapses to
the `U = 1` case the source says is already proved elsewhere. -/
abbrev UconfigRegPos (α : ℝ) := {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  witnessL // IsRegularHolonomy U α}

/-- ~~**`Uconfig := {U // IsRegularHolonomy U 0}`** — Bałaban's own regular-`U` restriction
(`RegularityHolonomy.lean`, ALREADY built, reused verbatim), at threshold `Mα₀ := 0`. Every
`coercive`-shaped statement quantified over THIS type is, by construction, only ever asked of
regular configurations — CMP99b p.428's own TRUE deferred claim, not the unrestricted one
stage-1 was convicted for.~~
**CORRECTED 2026-07-26 (`NonFlatBackground.isRegularHolonomy_zero_iff_flat`).** At threshold `0`
`IsRegularHolonomy U 0 ↔ ∀ p, holonomyElem U p = 1`: this type is EXACTLY THE FLAT SET, so a
statement quantified over it is a statement about flat backgrounds — i.e. about `U = 1` up to
gauge, which is the case CMP96 [4] Lemma 2.4 already proves and which p.428 explicitly sets aside
as *not* the deferred part. It is RETAINED (definitionally unchanged) so that nothing downstream
silently changes meaning, and it is now the `α = 0` member of a threshold-indexed family. The
non-degenerate domain is `UconfigRegPos α` for `α > 0` (§4b). -/
abbrev UconfigReg := UconfigRegPos (0 : ℝ)

/-- **`IsRegularHolonomy` is monotone in the threshold** (a two-line fact this tree did not have;
`grep` first, LAW-19). It is what lets every `UconfigReg` element be promoted into
`UconfigRegPos α` for `α ≥ 0`, so re-indexing LOSES nothing. -/
theorem isRegularHolonomy_mono
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL} {a b : ℝ}
    (h : IsRegularHolonomy U a) (hab : a ≤ b) : IsRegularHolonomy U b :=
  fun p => le_trans (h p) hab

/-- Promotion `UconfigReg ↪ UconfigRegPos α` for `0 ≤ α`: the flat set sits inside every
nonnegative-threshold regular set. -/
def UconfigRegPos.ofFlat {α : ℝ} (hα : 0 ≤ α) (U : UconfigReg) : UconfigRegPos α :=
  ⟨U.val, isRegularHolonomy_mono U.property hα⟩

/-- **`trivialU` and `pureGaugeU`, BOTH regular at `Mα₀=0`, packaged as elements of
`UconfigReg`** — `trivialU_isRegularHolonomy`/`pureGaugeU_isRegularHolonomy_zero`, both reused
verbatim (LAW-19).
⚠ **ADDED 2026-07-26 (nothing struck here — the docstring above never overclaimed, it simply did
not say this): BOTH WITNESSES ARE FLAT** (`NonFlatBackground.pureGaugeU_holonomy_eq_one`), so the
`Nontrivial UconfigReg` instance they inhabit separates gauge representatives and nothing else —
`uReg0_ne_uReg1_is_gauge_variant` below. The "GENUINELY NON-FLAT" overclaim about `pureGaugeU`
lives in `RegularityHolonomy.lean`'s own docstrings (outside this file's write scope), where it is
already banner-corrected. -/
noncomputable def uReg0 : UconfigReg := ⟨trivialU witnessL, trivialU_isRegularHolonomy le_rfl⟩

noncomputable def uReg1 : UconfigReg := ⟨pureGaugeU, pureGaugeU_isRegularHolonomy_zero⟩

theorem uReg0_ne_uReg1 : uReg0 ≠ uReg1 := by
  intro h
  have hval : (trivialU witnessL) = pureGaugeU := congrArg Subtype.val h
  have h0 : (pureGaugeU (witnessY, (0 : Fin 3)) : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 1 := by
    rw [← hval]; rfl
  exact pureGaugeU_ne_trivial h0

instance : Nontrivial UconfigReg := ⟨uReg0, uReg1, uReg0_ne_uReg1⟩

#print axioms uReg0_ne_uReg1
#print axioms UconfigRegPos
#print axioms isRegularHolonomy_mono
#print axioms UconfigRegPos.ofFlat

/-! ### §4a — THE DEFECT, AS A THEOREM IN THE FILE THAT CARRIED IT

The two statements below are what turn the 2026-07-26 finding from prose into kernel-checked
record. They are the reason `Nontrivial UconfigReg` firing green proves nothing about
non-degeneracy. -/

/-- **EVERY element of `UconfigReg` is FLAT.** Direct from
`NonFlatBackground.isRegularHolonomy_zero_iff_flat`. -/
theorem UconfigReg_all_flat (U : UconfigReg) (p : PeriodicLatticePlaquette witnessL) :
    holonomyElem U.val p = 1 :=
  (isRegularHolonomy_zero_iff_flat U.val).mp U.property p

/-- **`UconfigReg` contains NO curved configuration** — the domain of every `∀ U : UconfigReg`
statement in this file is curvature-free. -/
theorem no_curved_mem_UconfigReg :
    ¬ ∃ U : UconfigReg, ∃ p : PeriodicLatticePlaquette witnessL, holonomyElem U.val p ≠ 1 := by
  rintro ⟨U, p, hp⟩
  exact hp (UconfigReg_all_flat U p)

/-- **THE LESSON, AS A THEOREM: `uReg0 ≠ uReg1` is a GAUGE-VARIANT separation.** The two witnesses
that make `Nontrivial UconfigReg` fire differ only in a bare link value; their CURVATURES are
identical (both identically `1`). A control of this shape cannot detect that its domain is
degenerate, because the property it tests is not the property at issue. -/
theorem uReg0_ne_uReg1_is_gauge_variant :
    uReg0 ≠ uReg1 ∧
      (∀ p : PeriodicLatticePlaquette witnessL,
        holonomyElem uReg0.val p = holonomyElem uReg1.val p) :=
  ⟨uReg0_ne_uReg1, fun p => by
    rw [UconfigReg_all_flat uReg0 p, UconfigReg_all_flat uReg1 p]⟩

#print axioms UconfigReg_all_flat
#print axioms no_curved_mem_UconfigReg
#print axioms uReg0_ne_uReg1_is_gauge_variant

/-! ### §4b — POPULATING `UconfigRegPos α` NON-DEGENERATELY, AT EVERY POSITIVE THRESHOLD

**No threshold is invented here.** The statements below are proved for an ARBITRARY `α > 0`, so
this file commits to no numeric smallness constant of its own — whatever threshold a consumer
needs, the domain is non-degenerate at it. The link to the perturbative regime is made
QUANTITATIVE rather than asserted: the exhibited inhabitant satisfies
`α₁ := frobSupBond U ≤ √α`, where `α₁ = sup_b ‖U(b) − 1‖_F` is exactly the quantity
`RegularUPerturbation`'s `[L2-AGG]` estimates are stated in
(`norm_curlDrift_L2_le_sup`, `abs_deltaJ_sub_L2_le_sup`). So `α ↓ 0` drives `α₁ ↓ 0` while the
curvature stays nonzero.

**Honest scope note on "the regime `[L2-AGG]` consumes".** `RegularUPerturbation`'s `[L2-AGG]`
lemmas carry NO smallness hypothesis on `α₁` — they are proved for every `α₁`. The smallness is
consumed one level up, by the geometric series (3.86) `G(U'U) = G(U)(I − V(A)G(U))⁻¹`, which is
NOT formalized in this tree. So "small enough for `[L2-AGG]`" is, as of today, satisfied by every
`α > 0`; the `≤ √α` clause is stated anyway because it is the bound the unformalized step will
need, and stating it now is what makes the choice of `α` audit-able later. -/

/-- **`[CTRL-CURVED-REGULAR]` — THE NON-DEGENERACY CONTROL `Nontrivial` COULD NOT PROVIDE.**
For EVERY `α > 0` the subtype `UconfigRegPos α` contains a configuration that

* has NONZERO CURVATURE at some plaquette (`holonomyElem ≠ 1`) — the discriminating property;
* is not the gauge transform, by ANY `γ`, of ANY configuration flat at `witnessPlaquette` — so
  the separation from the flat sector is GAUGE-INVARIANT, not a bare link value (this is exactly
  what `uReg0 ≠ uReg1` failed to be, `uReg0_ne_uReg1_is_gauge_variant`);
* has `α₁ = frobSupBond U ≤ √α`, tying the threshold to the perturbative parameter;
* is `κ`-separated from the flat reference (§3b), so it is directly usable as a
  `Δ_nonconstant` witness — the fourth clause is what makes §10b's instance carry a
  FLAT-vs-CURVED variation rather than a gauge-representative one.

Contrast `no_curved_mem_UconfigReg`: at `α = 0` no such inhabitant exists, for any witness.

**OPS-3 — how this fails.** It is FALSE at `α = 0` (`no_curved_mem_UconfigReg` is its exact
negation there), and `hα : 0 < α` is consumed by `exists_curved_regular_below`, which produces a
`t ≠ 0` only because it can fit `8t²/(1+t²)` strictly under a POSITIVE `α`. Clause 4 fails at
`t = 0` (`kappa_nonflatU_ne_trivialU`'s own hypothesis), clause 3 fails if
`frobSupBond_nonflatU`'s exact value `√(8t²/(1+t²))` is replaced by any larger quantity. -/
theorem exists_curved_mem_UconfigRegPos {α : ℝ} (hα : 0 < α) :
    ∃ U : UconfigRegPos α,
      (∃ p : PeriodicLatticePlaquette witnessL, holonomyElem U.val p ≠ 1) ∧
      (∀ (γ : PeriodicLatticeSite witnessL → Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (W : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL),
          holonomyElem W witnessPlaquette = 1 → U.val ≠ periodicGaugeTransform γ W) ∧
      frobSupBond U.val ≤ Real.sqrt α ∧
      kappa U.val ≠ kappa (trivialU witnessL) := by
  obtain ⟨t, ht, hreg, hsmall, _hcurv⟩ := exists_curved_regular_below hα
  refine ⟨⟨nonflatU t, isRegularHolonomy_mono hreg hsmall.le⟩,
    nonflatU_has_curved_plaquette ht,
    fun γ W hW => nonflatU_not_gaugeTransform_of_flat ht γ W hW, ?_,
    kappa_nonflatU_ne_trivialU ht⟩
  rw [frobSupBond_nonflatU]
  exact Real.sqrt_le_sqrt hsmall.le

#print axioms exists_curved_mem_UconfigRegPos

/-- The curved inhabitant, as a term (`Classical.choose` of the control above), so downstream
constructions can name it. -/
noncomputable def uRegCurved {α : ℝ} (hα : 0 < α) : UconfigRegPos α :=
  Classical.choose (exists_curved_mem_UconfigRegPos hα)

theorem uRegCurved_curved {α : ℝ} (hα : 0 < α) :
    ∃ p : PeriodicLatticePlaquette witnessL, holonomyElem (uRegCurved hα).val p ≠ 1 :=
  (Classical.choose_spec (exists_curved_mem_UconfigRegPos hα)).1

theorem uRegCurved_not_gaugeTransform_of_flat {α : ℝ} (hα : 0 < α)
    (γ : PeriodicLatticeSite witnessL → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (W : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hW : holonomyElem W witnessPlaquette = 1) :
    (uRegCurved hα).val ≠ periodicGaugeTransform γ W :=
  (Classical.choose_spec (exists_curved_mem_UconfigRegPos hα)).2.1 γ W hW

theorem uRegCurved_frobSupBond_le {α : ℝ} (hα : 0 < α) :
    frobSupBond (uRegCurved hα).val ≤ Real.sqrt α :=
  (Classical.choose_spec (exists_curved_mem_UconfigRegPos hα)).2.2.1

theorem uRegCurved_kappa_ne {α : ℝ} (hα : 0 < α) :
    kappa (uRegCurved hα).val ≠ kappa (trivialU witnessL) :=
  (Classical.choose_spec (exists_curved_mem_UconfigRegPos hα)).2.2.2

/-- **`trivialU` is in every nonnegative-threshold regular set** — the flat reference point. -/
noncomputable def uRegFlat {α : ℝ} (hα : 0 ≤ α) : UconfigRegPos α :=
  ⟨trivialU witnessL, trivialU_isRegularHolonomy hα⟩

/-- **The two witnesses differ, AND THE SEPARATING INVARIANT IS THE CURVATURE** — the property
`uReg0 ≠ uReg1` could not have (`uReg0_ne_uReg1_is_gauge_variant`). -/
theorem uRegFlat_ne_uRegCurved {α : ℝ} (hα : 0 < α) : uRegFlat hα.le ≠ uRegCurved hα := by
  intro h
  obtain ⟨p, hp⟩ := uRegCurved_curved hα
  apply hp
  have hval : (uRegFlat hα.le).val = (uRegCurved hα).val := congrArg Subtype.val h
  rw [← hval]
  exact AdalyFormal.Balaban.DeltaPrime.holonomyElem_trivialU p

/-- **`Nontrivial (UconfigRegPos α)` for `α > 0`, WITNESSED BY A CURVATURE DIFFERENCE.** This is
the honest replacement for `instance : Nontrivial UconfigReg`: the two witnesses here are
separated by the gauge-INVARIANT plaquette holonomy, not by a bare link value. -/
theorem nontrivial_curved_UconfigRegPos {α : ℝ} (hα : 0 < α) : Nontrivial (UconfigRegPos α) :=
  ⟨uRegFlat hα.le, uRegCurved hα, uRegFlat_ne_uRegCurved hα⟩

#print axioms uRegCurved
#print axioms uRegFlat
#print axioms uRegCurved_curved
#print axioms uRegCurved_not_gaugeTransform_of_flat
#print axioms uRegCurved_frobSupBond_le
#print axioms uRegCurved_kappa_ne
#print axioms uRegFlat_ne_uRegCurved
#print axioms nontrivial_curved_UconfigRegPos

/-! ## §5 — `sourceCorrection`: CONCRETE, closed form, `J ≠ 0` REQUIRED (defect (b)'s fix) -/

/-- **`H₁ = id`, UNCONDITIONALLY** — a disclosed CONSEQUENCE of the inherited `Q:=Qstar:=1`
simplification (`Q=Qstar=1` forces `Gstar∘Qstar∘CompInv = Gstar∘id∘Ginv = id` by
`GstarSU2_GinvSU2`), mirroring `RegularUCoercivity.solutionOperator_deltaKUnifiedData_eq_id`'s
identical mechanism one level over (module docstring, "WHAT IS EXPLICITLY INHERITED"). -/
theorem solutionOperator_su2_eq_id
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (x : BFL2 witnessL) : solutionOperator (su2CovarianceData U) x = x := by
  rw [solutionOperator_apply]
  show GstarSU2 U ((1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) (GinvSU2 U x)) = x
  rw [ContinuousLinearMap.one_apply]
  exact GstarSU2_GinvSU2 U x

/-- **`sourceCorrection`, CONCRETE closed form.** `v0`,`J` fixed; `Qext := qextQuad v0`
(`RegularUCoercivity.lean`, LAW-19); `c := -2⟪H₁(v0),J⟫` (`= -2⟪v0,J⟫` by `solutionOperator_
su2_eq_id`, but built via `solutionOperator` for traceability to (3.156)'s own `H₁` symbol). -/
noncomputable def sourceCorrectionSU2 (U : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (v0 J : BFL2 witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (-2 * (inner ℝ (solutionOperator (su2CovarianceData U) v0) J : ℝ)) •
    (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)

/-- **THE FIDELITY IDENTITY, PROVED**: `⟪v,sourceCorrection v⟫` EQUALS (3.156)'s own third-term
value `-2⟪H₁(D̃²(Qext,v)),J⟫`, exactly — not merely typed, computed. -/
theorem sourceCorrectionSU2_eq (U : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (v0 J v : BFL2 witnessL) :
    (inner ℝ v (sourceCorrectionSU2 U v0 J v) : ℝ) =
      -2 * (inner ℝ (solutionOperator (su2CovarianceData U)
        (Dtilde2Shape (qextQuad v0) v)) J : ℝ) := by
  unfold sourceCorrectionSU2
  show (inner ℝ v ((-2 * (inner ℝ (solutionOperator (su2CovarianceData U) v0) J : ℝ)) • v) : ℝ)
    = _
  rw [real_inner_smul_right, dtilde2_qextQuad, solutionOperator_su2_eq_id,
    solutionOperator_su2_eq_id, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  ring

#print axioms solutionOperator_su2_eq_id
#print axioms sourceCorrectionSU2_eq

/-! ## §6 — `deltaKBaseOf_su2`/`deltaKCOf_su2`: (3.156)/(3.157) assembled -/

/-- **`Δ_k(U)`'s BASE part**, CMP99b (3.156): `(QG₁Q*)⁻¹ − a·id + sourceCorrection`, with the
first term now GENUINELY `U`-dependent (§2), not the inherited constant. -/
noncomputable def deltaKBaseOfSU2 (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  (su2CovarianceData U).CompInv - usedAt bc 0 • (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) +
    sourceCorrectionSU2 U v0 J

/-! ## §7 — `ReparamDataSU2`: defect (c)'s fix — `C` genuinely constrained -/

/-- **`subspace156BFL2` is a PROPER subspace, for EVERY `U`** — from `Q1Real.q1RealKernel_ne_top`
(unconditional in `U`, already proved) via `⊓`'s monotonicity, transported along the surjective
`bfl2Equiv`. This is what makes defect (c)'s image-containment obligation genuinely exclude
`id`. -/
theorem subspace156G_ne_top (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    AdalyFormal.Balaban.DeltaKUnified.subspace156G Lambda S' ell U ≠ ⊤ := by
  intro htop
  apply q1RealKernel_ne_top U
  have hle : AdalyFormal.Balaban.DeltaKUnified.subspace156G Lambda S' ell U ≤ q1RealKernel U :=
    inf_le_right
  rw [htop] at hle
  exact top_le_iff.mp hle

theorem subspace156BFL2_ne_top (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    subspace156BFL2 Lambda S' ell U ≠ ⊤ := by
  intro htop
  apply subspace156G_ne_top Lambda S' ell U
  ext b
  simp only [Submodule.mem_top, iff_true]
  have hmem : (bfl2Equiv (Lat := witnessL)).symm b ∈ subspace156BFL2 Lambda S' ell U :=
    htop ▸ Submodule.mem_top
  have hmem2 : (bfl2Equiv (Lat := witnessL)).toLinearMap
      ((bfl2Equiv (Lat := witnessL)).symm b) ∈
      AdalyFormal.Balaban.DeltaKUnified.subspace156G Lambda S' ell U := hmem
  simpa using hmem2

#print axioms subspace156G_ne_top
#print axioms subspace156BFL2_ne_top

/-- **`C`, `C*`: a genuine adjoint pair whose IMAGE lies in the (proper) admissible subspace, and
which RETRACTS onto it** — CMP99b (3.157)'s own "almost-local reparametrization onto the
subspace" role, made a checkable Lean obligation (not a free field). -/
structure ReparamDataSU2 (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) where
  C : BFL2 witnessL →L[ℝ] BFL2 witnessL
  Cadj : BFL2 witnessL →L[ℝ] BFL2 witnessL
  adjoint_law : ∀ v w, (inner ℝ (C v) w : ℝ) = inner ℝ v (Cadj w)
  image_admissible : ∀ v, C v ∈ subspace156BFL2 Lambda S' ell U
  retraction : ∀ v ∈ subspace156BFL2 Lambda S' ell U, C v = v

/-- **`C := id` is STRUCTURALLY EXCLUDED** — `image_admissible` for `C:=id` would force
`subspace156BFL2 = ⊤` (every vector is its own image), contradicting `subspace156BFL2_ne_top`.
This is the direct repair of stage-1's collapse: `id` is not merely shown to break the bound, it
cannot even INHABIT `ReparamDataSU2`. -/
theorem reparamDataSU2_blocks_id (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ¬ ∃ RD : ReparamDataSU2 Lambda S' ell U, RD.C = (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by
  rintro ⟨RD, hC⟩
  apply subspace156BFL2_ne_top Lambda S' ell U
  ext v
  simp only [Submodule.mem_top, iff_true]
  have := RD.image_admissible v
  rwa [hC, ContinuousLinearMap.one_apply] at this

/-- **`C := 0` is ALSO STRUCTURALLY EXCLUDED**, whenever the target subspace is nonzero
(`subspace156BFL2_ne_bot`, at the fixed `Lambda:=univ,S':=∅,ell:=witnessEll,U:=trivialU`
instantiation): `retraction` forces `0 = v` for the nonzero witness `v`. -/
theorem reparamDataSU2_blocks_zero :
    ¬ ∃ RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        RD.C = (0 : BFL2 witnessL →L[ℝ] BFL2 witnessL) := by
  rintro ⟨RD, hC⟩
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot subspace156BFL2_ne_bot
  have hret := RD.retraction v hvmem
  rw [hC, ContinuousLinearMap.zero_apply] at hret
  exact hvne hret.symm

#print axioms reparamDataSU2_blocks_id
#print axioms reparamDataSU2_blocks_zero

/-- **A CONCRETE, non-degenerate witness of `ReparamDataSU2`**: the orthogonal projection onto
`subspace156BFL2` itself. Self-adjoint (`inner_starProjection_left_eq_right`, Mathlib,
already-proved general fact — not built here), image-containing (`starProjection_apply_mem`),
retracting (`starProjection_eq_self_iff`) — ALL THREE obligations discharged by ONE standard
Hilbert-space construction, `sorry`-free. -/
noncomputable def reparamDataSU2Witness (Lambda S' : Finset (PeriodicLatticeSite witnessL))
    (ell : ℕ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ReparamDataSU2 Lambda S' ell U where
  C := (subspace156BFL2 Lambda S' ell U).starProjection
  Cadj := (subspace156BFL2 Lambda S' ell U).starProjection
  adjoint_law := fun v w =>
    Submodule.inner_starProjection_left_eq_right (subspace156BFL2 Lambda S' ell U) v w
  image_admissible := fun v => Submodule.starProjection_apply_mem _ v
  retraction := fun v hv => Submodule.starProjection_eq_self_iff.mpr hv

#print axioms reparamDataSU2Witness

/-! ## §8 — `deltaKC_su2`: the full `C*Δ_kC` assembly. `RD` (the reparametrization) is FIXED at
the reference subspace `subspace156BFL2 ... (trivialU witnessL)` — matching CMP99b (3.157)'s own
role for `C` (a per-scale reparametrization, not re-chosen per background) — while
`deltaKBaseOfSU2 bc v0 J U` genuinely varies with `U`. -/

/-- **`C*Δ_kC`, CMP99b (3.156)/(3.157) literally, over the su(2) carrier.** -/
noncomputable def deltaKC_su2 (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    BFL2 witnessL →L[ℝ] BFL2 witnessL :=
  RD.Cadj ∘L (deltaKBaseOfSU2 bc v0 J U) ∘L RD.C

theorem deltaKC_su2_apply (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) :
    deltaKC_su2 bc v0 J Lambda S' ell RD U v =
      RD.Cadj (deltaKBaseOfSU2 bc v0 J U (RD.C v)) := rfl

#print axioms deltaKC_su2_apply

/-! ## §9 — `Δ_nonconstant`, PROVED (defect (a)'s headline consequence): genuine `κ(U)`-variation
survives the `C*·C` sandwich, at any nonzero point FIXED by `RD.C` (in particular the reference
subspace's own nonzero witness, `subspace156BFL2_ne_bot`). -/

/-- **At any `v` FIXED by `RD.C`, `deltaKC_su2`'s value is `scalar(U) • RD.Cadj v`**, the scalar
carrying `κ(U)`'s genuine variation (§2) and the SOURCE term's `H₁ = id`-forced, `U`-independent
contribution (§5's own disclosure). -/
theorem deltaKC_su2_at_fixed_point (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) (hv : RD.C v = v) :
    deltaKC_su2 bc v0 J Lambda S' ell RD U v =
      ((baseG + kappa U)⁻¹ - usedAt bc 0 +
          (-2 * (inner ℝ (solutionOperator (su2CovarianceData U) v0) J : ℝ))) • RD.Cadj v := by
  rw [deltaKC_su2_apply, hv]
  unfold deltaKBaseOfSU2
  show RD.Cadj ((su2CovarianceData U).CompInv v - usedAt bc 0 • v + sourceCorrectionSU2 U v0 J v)
    = _
  have h1 : (su2CovarianceData U).CompInv v = (baseG + kappa U)⁻¹ • v := rfl
  have h2 : sourceCorrectionSU2 U v0 J v =
      (-2 * (inner ℝ (solutionOperator (su2CovarianceData U) v0) J : ℝ)) • v := rfl
  rw [h1, h2, ← sub_smul, ← add_smul, map_smul]

#print axioms deltaKC_su2_at_fixed_point

/-- **`RD.Cadj v ≠ 0`, for a nonzero `v` FIXED by `RD.C`** — from the adjoint law:
`⟪v,RD.Cadj v⟫ = ⟪RD.C v,v⟫ = ⟪v,v⟫ = ‖v‖² > 0`, so `RD.Cadj v = 0` would force `0 > 0`. -/
theorem reparamCadj_ne_zero_of_fixed
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (v : BFL2 witnessL) (hv : RD.C v = v) (hvne : v ≠ 0) : RD.Cadj v ≠ 0 := by
  intro hcontra
  have h1 : (inner ℝ v (RD.Cadj v) : ℝ) = inner ℝ (RD.C v) v := (RD.adjoint_law v v).symm
  rw [hv, hcontra, inner_zero_right] at h1
  have h2 : (0 : ℝ) < (inner ℝ v v : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    have hpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hvne
    positivity
  rw [← h1] at h2
  exact lt_irrefl 0 h2

#print axioms reparamCadj_ne_zero_of_fixed

/-- **`Δ_nonconstant`, IN ITS GENERAL FORM: any `κ`-separated pair separates the sandwiched
operator.** Generalized 2026-07-26 from the `trivialU`/`pureGaugeU` special case below, so that a
FLAT-vs-CURVED pair can be used (§9b) — the pair the original statement should have used and
could not, because at threshold `0` no curved configuration is admissible at all
(`no_curved_mem_UconfigReg`). -/
theorem deltaKC_su2_nonconstant_of_kappa_ne (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U₁ U₂ : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hκ : kappa U₁ ≠ kappa U₂)
    (v : BFL2 witnessL) (hv : RD.C v = v) (hvne : v ≠ 0) :
    deltaKC_su2 bc v0 J Lambda S' ell RD U₁ ≠ deltaKC_su2 bc v0 J Lambda S' ell RD U₂ := by
  intro hcontra
  have heval : deltaKC_su2 bc v0 J Lambda S' ell RD U₁ v =
      deltaKC_su2 bc v0 J Lambda S' ell RD U₂ v := by rw [hcontra]
  rw [deltaKC_su2_at_fixed_point bc v0 J Lambda S' ell RD U₁ v hv,
    deltaKC_su2_at_fixed_point bc v0 J Lambda S' ell RD U₂ v hv,
    solutionOperator_su2_eq_id, solutionOperator_su2_eq_id] at heval
  have hCadjNe := reparamCadj_ne_zero_of_fixed Lambda S' ell RD v hv hvne
  have hsub : (((baseG + kappa U₁)⁻¹ - usedAt bc 0 + (-2 * (inner ℝ v0 J : ℝ))) -
      ((baseG + kappa U₂)⁻¹ - usedAt bc 0 + (-2 * (inner ℝ v0 J : ℝ)))) • RD.Cadj v = 0 := by
    rw [sub_smul, heval]; abel
  rcases smul_eq_zero.mp hsub with h' | h'
  · have hrecip : (baseG + kappa U₁)⁻¹ = (baseG + kappa U₂)⁻¹ := by
      have := sub_eq_zero.mp h'; linarith
    have heq : baseG + kappa U₁ = baseG + kappa U₂ := by
      have hc := congrArg Inv.inv hrecip
      rwa [inv_inv, inv_inv] at hc
    exact hκ (by linarith)
  · exact hCadjNe h'

/-- ~~**THE HEADLINE THEOREM: `Δ_nonconstant`, PROVED — DERIVED from `Q1Real`'s real
`U`-dependence (via `κ`), never assumed.** At any nonzero `v` fixed by the (fixed)
reparametrization `RD.C`, the sandwiched operator genuinely differs between `trivialU` and
`pureGaugeU` — both `IsRegularHolonomy _ 0`-regular (§4), so this witnesses `Δ_nonconstant` FOR
THE REGULAR SUBTYPE `UconfigReg`.~~
**QUALIFIED 2026-07-26.** The statement is TRUE and is retained verbatim, but the variation it
exhibits is between two FLAT configurations (`NonFlatBackground.pureGaugeU_holonomy_eq_one`), and
"the REGULAR SUBTYPE `UconfigReg`" is the FLAT SET (`UconfigReg_all_flat`). So what it witnesses
is that `Δ` sees the choice of GAUGE REPRESENTATIVE — a weaker fact than it reads as. The
flat-vs-curved witness is `deltaKC_su2_nonconstant_curved` (§9b); the proof here is now a
one-line instance of `deltaKC_su2_nonconstant_of_kappa_ne` (LAW-19). -/
theorem deltaKC_su2_nonconstant (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (v : BFL2 witnessL) (hv : RD.C v = v) (hvne : v ≠ 0) :
    deltaKC_su2 bc v0 J Lambda S' ell RD (trivialU witnessL) ≠
      deltaKC_su2 bc v0 J Lambda S' ell RD pureGaugeU :=
  deltaKC_su2_nonconstant_of_kappa_ne bc v0 J Lambda S' ell RD _ _
    kappa_trivialU_ne_pureGaugeU v hv hvne

#print axioms deltaKC_su2_nonconstant_of_kappa_ne
#print axioms deltaKC_su2_nonconstant

/-! ### §9b — `Δ_nonconstant` ACROSS A CURVATURE DIFFERENCE (2026-07-26)

The variation of `Δ` is exhibited between the flat reference `trivialU` and the provably CURVED
`NonFlatBackground.nonflatU t`, both admissible in `UconfigRegPos α` once `α > 0`. This is what
`Δ_nonconstant` was supposed to say: the operator is not blind to the background's FIELD
STRENGTH. Note this is strictly stronger than the `trivialU`/`pureGaugeU` version, which only
shows `Δ` is not gauge-invariant. -/

/-- **`Δ` DIFFERS ACROSS A CURVATURE DIFFERENCE.**

**OPS-3 — how this fails.** At `t = 0` the two sides are the SAME configuration
(`nonflatU_zero_eq_trivial`) and the statement is false; `ht` is load-bearing, entering through
`kappa_nonflatU_ne_trivialU`. It also fails for any `v` outside the fixed-point set of `RD.C`
(`hv`), and at `v = 0` (`hvne`), both of which `reparamCadj_ne_zero_of_fixed` consumes. -/
theorem deltaKC_su2_nonconstant_curved (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    {t : ℝ} (ht : t ≠ 0)
    (v : BFL2 witnessL) (hv : RD.C v = v) (hvne : v ≠ 0) :
    deltaKC_su2 bc v0 J Lambda S' ell RD (nonflatU t) ≠
      deltaKC_su2 bc v0 J Lambda S' ell RD (trivialU witnessL) :=
  deltaKC_su2_nonconstant_of_kappa_ne bc v0 J Lambda S' ell RD _ _
    (kappa_nonflatU_ne_trivialU ht) v hv hvne

#print axioms deltaKC_su2_nonconstant_curved

/-- **Corollary, packaged in `CoercivityHypothesis.Δ_nonconstant`'s exact shape**, using the
CONCRETE `reparamDataSU2Witness` at `trivialU` (self-adjoint orthogonal projection, `sorry`-free,
§7) and the nonzero witness `subspace156BFL2_ne_bot` supplies. -/
theorem deltaKC_su2_nonconstant_exists (bc : BaseConstant) (v0 J : BFL2 witnessL) :
    ∃ (k : ℕ) (U₁ U₂ : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL),
      U₁ ≠ U₂ ∧
      deltaKC_su2 bc v0 J (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
          AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
          (reparamDataSU2Witness Finset.univ ∅ AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
            (trivialU witnessL)) U₁ ≠
        deltaKC_su2 bc v0 J (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
          AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
          (reparamDataSU2Witness Finset.univ ∅ AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
            (trivialU witnessL)) U₂ := by
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot subspace156BFL2_ne_bot
  refine ⟨0, trivialU witnessL, pureGaugeU, ?_, ?_⟩
  · intro h
    apply pureGaugeU_ne_trivial
    have h0 : (pureGaugeU (witnessY, (0 : Fin 3)) : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 1 := by
      rw [← h]; rfl
    rw [h0]
  · exact deltaKC_su2_nonconstant bc v0 J Finset.univ ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
      (reparamDataSU2Witness Finset.univ ∅ AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
        (trivialU witnessL))
      v (Submodule.starProjection_eq_self_iff.mpr hvmem) hvne

#print axioms deltaKC_su2_nonconstant_exists

/-! ## §10 — `faithfulCoercivityHypothesisSU2`: THE DELIVERABLE, assembling `CoercivityHypothesis
(BFL2 witnessL) UconfigReg`, defect (a)'s FULL fix -/

/-- **THE ONE HONEST SORRY, `[LEM-COERC-U-GAMMA0-SU2]`.** CMP99b p.428, verbatim: "It is more
convenient to work with the operator `C̄^{(k)}(Λ)` ... a positive definite operator `C*Δ_kC` with
a lower bound `γ₀ > 0` independent of `k` and `U`. We have proved it in [4], Lemma 2.4, for
operators with `U = 1`. Localizing the operators in `Δ_k` and using the methods of Sect. B we can
prove it for `C*Δ_kC` with an arbitrary configuration `U` satisfying (3.35),(3.36) with `Mα₀`
sufficiently small." `U = 1` (`trivialU`) is PROVED in the source (CMP96 [4] Lemma 2.4); the
~~regular-`U` case (`Uconfig` HERE already restricted to `IsRegularHolonomy _ 0`, §4) is ASSERTED
with a named method NEVER carried out ("using the methods of Sect. B") — the genuine, bounded
formalization task.~~
⚠ **CORRECTED 2026-07-26: THE STATEMENT BELOW IS THE `U = 1` CASE, NOT THE DEFERRED ONE.** `U`
ranges over `UconfigReg`, and `UconfigReg` is the FLAT SET (`UconfigReg_all_flat`,
`no_curved_mem_UconfigReg`, from `NonFlatBackground.isRegularHolonomy_zero_iff_flat`). `Mα₀ = 0`
is not "sufficiently small", it is DEGENERATE — the quoted sentence's own contrast with "[4],
Lemma 2.4, for operators with `U = 1`" collapses at `Mα₀ = 0`, because up to gauge the flat set
IS `U = 1`. The statement is RETAINED VERBATIM (so nothing downstream silently changes meaning)
and is now labelled for what it is; the non-degenerate domain is `UconfigRegPos α`, `α > 0`
(§4b), and §10b reports in full what happens on re-targeting there. Note also the module
banner: this `sorry` is separately CONVICTED FALSE-AS-TYPED for a reason that has nothing to do
with the domain (`bc.a` free) — see §10b item 4, which makes the missing gate exact.

⚠⚠ **REFUTED IN THE KERNEL 2026-07-28 (faithful_chain lane).** The conviction above is now a
theorem: `FaithfulRepairSU2Gamma.gamma_exists_su2_refuted` exhibits `bc.a := 2`, `v0 := J := w`
(any nonzero `w ∈ subspace156BFL2`), `RD := reparamDataSU2Witness` — every argument legal, this
theorem imposing no hypothesis on them — for which NO positive `γ` exists;
`FaithfulRepairSU2Gamma.gamma_exists_su2_statement_is_false` is this statement universally closed
over its four arguments and negated, sorryAx-free. The mechanism is
`inner_deltaKC_su2_eq_scalar` (§10b) plus the CEILING `(baseG+κ(U))⁻¹ ≤ 1`
(`FaithfulRepairSU2Gamma.inv_baseG_add_kappa_le_one`), mirroring §10b's own `1/3` floor. Per
L4/L5 the `sorry` below is neither closable nor axiom-isable and the statement must not be
weakened in place; it is RETAINED. **The repaired statement is
`FaithfulRepairSU2Gamma.gamma_exists_su2_repaired`** (gate `usedAt bc 0 + 2⟪v0,J⟫ < 1/3`,
`γ := 1/3 − a − 2⟪v0,J⟫`, PROVED), and the drop-in sorry-free instance at this file's own type is
`FaithfulRepairSU2Gamma.faithfulCoercivityHypothesisSU2Repaired`. Consumers must migrate.

**Structural fix over stage-1**: `γ` is NOT a free parameter of this
statement (contrast stage-1's `faithfulCoercivityHypothesis`, which took `γ0 hγ0` as EXTERNAL
arguments — the exact mechanism `‖deltaKC SI 0 U₀‖+1` exploited, `VERDICT.md` §1). Here `γ` is
BOUND by the existential itself; there is no argument slot through which an adversary could
supply an operator-norm-derived counter-value. ⚠ **That claim is true of `γ` and was read as if it
made the statement safe. It does not: `bc`, `v0`, `J` are still free argument slots, and the
refutation above uses them.** Re-binding one free parameter relocates the defect; it does not
remove it. -/
theorem gamma_exists_su2 (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (k : ℕ) (U : UconfigReg),
      ∀ v ∈ subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKC_su2 bc v0 J
          (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
          AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD U.val v) : ℝ) := by
  sorry

#print axioms gamma_exists_su2

/-- **⚠⚠ RESTS ON A REFUTED STATEMENT (2026-07-28, faithful_chain lane).** `γ''`/`coercive` below
are `Classical.choose` of `gamma_exists_su2`, which `FaithfulRepairSU2Gamma.gamma_exists_su2_
refuted` proves FALSE; this definition therefore carries `sorryAx` and cannot be repaired in place
without weakening (L5). Use `FaithfulRepairSU2Gamma.faithfulCoercivityHypothesisSU2Repaired` — same
type, same `Δ`, `V`, `V_ne_bot`, `Δ_nonconstant`, sorry-free `coercive`, explicit `γ''`. Retained,
not deleted, because downstream modules reference it and deleting the record would erase the
defect's history.

**THE DELIVERABLE (original text).** `Δ`, `V`, `V_ne_bot`, `Δ_nonconstant` — PROVED, `sorry`-free,
`Δ_nonconstant` DERIVED from `Q1Real`'s real `U`-dependence (§9), not assumed. ~~`coercive`/`γ''`
are the ONE honest, structurally-un-exploitable deferred claim (`gamma_exists_su2`).~~ **STRUCK:
"structurally-un-exploitable" was true of `γ` and false of the statement — see §10's banner.**
`V` is CMP96 (2.121)'s
own admissible subspace (`subspace156BFL2`, `DeltaKUnified.lean`, reused verbatim — NOT rebuilt
here, matching the dispatch's deliverable #4 via direct reuse: `subspace156BFL2`'s own docstring
already states its `Q₁`-clause is the REAL `Q1Real.q1RealKernel`, matching CMP96 (2.121)). -/
noncomputable def faithfulCoercivityHypothesisSU2
    (bc : BaseConstant) (v0 J : BFL2 witnessL) (_hJ : J ≠ 0)
    (RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)) :
    AdalyFormal.Balaban.CoercivityHypothesis (BFL2 witnessL) UconfigReg where
  Δ := fun _ U => deltaKC_su2 bc v0 J (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
    AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD U.val
  V := subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
    AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)
  V_ne_bot := subspace156BFL2_ne_bot
  Δ_nonconstant := by
    obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot subspace156BFL2_ne_bot
    exact ⟨0, uReg0, uReg1, uReg0_ne_uReg1,
      deltaKC_su2_nonconstant bc v0 J Finset.univ ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD v (RD.retraction v hvmem) hvne⟩
  γ'' := Classical.choose (gamma_exists_su2 bc v0 J RD)
  γ''_pos := (Classical.choose_spec (gamma_exists_su2 bc v0 J RD)).1
  coercive := fun k U v hv => (Classical.choose_spec (gamma_exists_su2 bc v0 J RD)).2 k U v hv

#print axioms faithfulCoercivityHypothesisSU2

/-! ## §10b — DID THE COERCIVITY CLAIM SURVIVE RE-TARGETING AT `α > 0`? (2026-07-26)

**Answer: yes, completely — and THAT is the finding.** There is no step in this file's
construction that uses flatness, so there is no "step X that breaks at nonzero curvature" to
report. Set out precisely:

1. **There is no coercivity PROOF here to survive or break.** `gamma_exists_su2` (§10) is a
   `sorry`. Re-typing its quantifier domain changes nothing about its provability.
2. **`Δ`'s entire `U`-dependence runs through `κ(U)`** (§2/§6), and `κ`'s bound
   `|κ(U)| ≤ ‖suTwoWitness‖² = 1` (`kappa_bound` + `norm_suTwoWitness_sq`) is UNIFORM OVER ALL
   `U`: its derivation is Cauchy-Schwarz plus `RMap`'s isometry, and consumes NO regularity
   hypothesis, at any threshold.
3. **Hence the regularity restriction is INERT for this `Δ`.** `deltaKC_su2_uniform_lower_bound`
   below proves the bound `(1/3 − a − 2⟪v0,J⟫)‖v‖² ≤ ⟪v, Δv⟫` for an ARBITRARY `U` — no
   `IsRegularHolonomy` anywhere in its statement, and no hypothesis on `bc` either: the
   inequality is UNCONDITIONAL. Re-indexing the domain from `α = 0` to `α > 0` therefore costs
   nothing and BUYS nothing about coercivity; what it buys is a domain that is no longer
   degenerate (§4b), which is what makes `Δ_nonconstant` and every future non-degeneracy control
   able to fail.
4. **What is genuinely missing is not about `U` at all, and is not part of the inequality.** The
   bound of item 3 is only COERCIVITY when its constant is POSITIVE, and that is the `bc.a` gate
   the 2026-07-23 prosecution named (module banner): `bc.a` is a caller-supplied argument
   restricted only by `0 < bc.a`, so `bc.a := 2` makes the constant negative and the bound
   vacuous, for EVERY `U`, regular or not. Made exact here: the gate is
   `usedAt bc 0 + 2⟪v0,J⟫ < 1/3`, the `1/3` being `(baseG + κ)⁻¹`'s uniform lower bound over all
   `U` (`inv_baseG_add_kappa_ge`, from `baseG = 2` and `|κ| ≤ 1`).

~~**WHY THE `sorry` IS NOT CLOSED HERE, THOUGH IT NEARLY COULD BE.**~~
⚠ **CORRECTED 2026-07-28 (faithful_chain lane): the `sorry` is not closable AT ALL, near or
otherwise — `gamma_exists_su2` as typed is FALSE
(`FaithfulRepairSU2Gamma.gamma_exists_su2_statement_is_false`). "Nearly could be" describes the
GATED statement, which is a different proposition and is now proved separately as
`FaithfulRepairSU2Gamma.gamma_exists_su2_repaired`. The paragraph below is retained struck because
its mathematical content (what the gated bound would and would not mean) is correct and still
governs the repaired form.**

~~`gamma_exists_su2` follows from `deltaKC_su2_uniform_lower_bound` the moment the gate is assumed~~
(that is exactly how `coercivityHypothesisSU2Pos_ofGate`'s `γ''_pos` is discharged).
Adding the hypothesis and declaring the `sorry` discharged would bank — under a name that reads
as Bałaban's regular-`U` coercivity — a statement whose entire content on `V` is the SCALAR
`(baseG+κ(U))⁻¹ − a − 2⟪v0,J⟫` times `‖v‖²`. That scalarization is not a suspicion: it is
`inner_deltaKC_su2_eq_scalar` below, the 2026-07-23 prosecution's "scalarization CONFIRMED, zero
residual operator content" re-proved in the kernel. The residual standing between this file and
p.428 is OPERATOR FAITHFULNESS (`[LEM-Q1REAL-ADJOINT]`, module docstring "NAMED, NOT BUILT"),
not the quantifier domain and not the gate. So the `sorry` stays, relabelled (§10), and the
gated statement below is shipped under its own name with its own honest reading. -/

/-- `baseG + κ(U) ≤ 3` for every `U`, from `baseG = 2` and `|κ(U)| ≤ ‖w‖² = 1`. -/
theorem baseG_add_kappa_le_three
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    baseG + kappa U ≤ 3 := by
  have h := kappa_bound U
  rw [norm_suTwoWitness_sq, abs_le] at h
  rw [baseG_eq_two]
  linarith [h.2]

/-- **THE UNIFORM SCALAR FLOOR, over ALL `U`**: `(baseG + κ(U))⁻¹ ≥ 1/3`. No regularity is used.
This is the quantitative form of §10b item 2, and the source of the `1/3` in the gate.

**OPS-3 — how this fails.** It is exactly sharp given `|κ| ≤ 1`: replace `baseG := ‖w‖² + 1` by
`‖w‖² + 2` (i.e. `baseG = 3`) and the floor becomes `1/4`, so the numeral is not free-floating —
`baseG_eq_two` is load-bearing and is itself pinned by `SuTwoInner.inner_eq_trace`'s
normalization (`inner_suTwoWitness_self`). Drop `kappa_bound` and there is no floor at all. -/
theorem inv_baseG_add_kappa_ge
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (1 / 3 : ℝ) ≤ (baseG + kappa U)⁻¹ := by
  have h1 : (1 : ℝ) ≤ baseG + kappa U := baseG_add_kappa_pos U
  have h3 : baseG + kappa U ≤ 3 := baseG_add_kappa_le_three U
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- **THE SCALARIZATION, IN THE KERNEL.** On any `v` fixed by the reparametrization `RD.C` — in
particular on all of `V`, by `RD.retraction` — the quadratic form of `C*Δ_kC` is EXACTLY a scalar
multiple of `‖v‖²`, the scalar being `(baseG+κ(U))⁻¹ − a − 2⟪v0,J⟫`. There is no residual
operator content. This re-proves in Lean the 2026-07-23 prosecution's central finding, which
until now lived only in the module banner's prose, and it is the reason §10b declines to close
the `sorry`. -/
theorem inner_deltaKC_su2_eq_scalar (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) (hv : RD.C v = v) :
    (inner ℝ v (deltaKC_su2 bc v0 J Lambda S' ell RD U v) : ℝ) =
      ((baseG + kappa U)⁻¹ - usedAt bc 0 + (-2 * (inner ℝ v0 J : ℝ))) * ‖v‖ ^ 2 := by
  rw [deltaKC_su2_at_fixed_point bc v0 J Lambda S' ell RD U v hv, solutionOperator_su2_eq_id,
    real_inner_smul_right]
  have h : (inner ℝ v (RD.Cadj v) : ℝ) = ‖v‖ ^ 2 := by
    have hadj := RD.adjoint_law v v
    rw [hv] at hadj
    rw [← hadj, real_inner_self_eq_norm_sq]
  rw [h]

/-- **THE UNIFORM LOWER BOUND, FOR ARBITRARY `U`, WITH NO HYPOTHESIS ON `bc` AT ALL.** Note what
is NOT in the statement: no `IsRegularHolonomy` at any threshold, and no gate on `bc.a` — the
inequality is UNCONDITIONAL. This is §10b item 3 as a theorem: the regularity restriction on
`Δ`'s domain is inert for this operator.

⚠ **NAMING CORRECTION, made by this lane against its own first draft (2026-07-26).** This theorem
was first written as `deltaKC_su2_coercive_of_gate` with an OPS-3 note claiming "drop `hgate` and
the conclusion is false". BOTH WERE WRONG: there is no `hgate` in the statement and the
conclusion holds unconditionally. The `bc.a` gate `usedAt bc 0 + 2⟪v0,J⟫ < 1/3` is needed for
exactly ONE thing — to make the CONSTANT `1/3 − a − 2⟪v0,J⟫` POSITIVE, i.e. for `γ''_pos` in
`coercivityHypothesisSU2Pos_ofGate`. It plays no role in the inequality. Recorded rather than
silently corrected: a lower bound with a negative constant is not coercivity, and a name that says
`coercive` invites exactly that conflation.

**OPS-3 — how this genuinely fails.** Replace `1/3` by any larger constant and it breaks:
`inv_baseG_add_kappa_ge` is attained in the limit `κ → +1` (`baseG + κ → 3`), so `1/3` is the
largest admissible floor given `kappa_bound`; the check that catches an inflated constant is the
`linarith` step against `h13`. Drop `hv` (equivalently, evaluate off `V`) and
`inner_deltaKC_su2_eq_scalar` no longer applies, since `RD.Cadj v` need not be `v` and the form
need not be a scalar multiple of `‖v‖²` at all. -/
theorem deltaKC_su2_uniform_lower_bound (bc : BaseConstant) (v0 J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (RD : ReparamDataSU2 Lambda S' ell (trivialU witnessL))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (v : BFL2 witnessL) (hv : RD.C v = v) :
    ((1 / 3 : ℝ) - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ)) * ‖v‖ ^ 2 ≤
      (inner ℝ v (deltaKC_su2 bc v0 J Lambda S' ell RD U v) : ℝ) := by
  rw [inner_deltaKC_su2_eq_scalar bc v0 J Lambda S' ell RD U v hv]
  have h13 := inv_baseG_add_kappa_ge U
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖v‖)

#print axioms baseG_add_kappa_le_three
#print axioms inv_baseG_add_kappa_ge
#print axioms inner_deltaKC_su2_eq_scalar
#print axioms deltaKC_su2_uniform_lower_bound

/-- **THE RE-TARGETED INSTANCE: `CoercivityHypothesis (BFL2 witnessL) (UconfigRegPos α)` for any
`α > 0`, `sorry`-FREE, given the `bc.a` gate.**

Read this correctly. What it establishes:
* the positive-threshold domain `UconfigRegPos α` is USABLE — a full `CoercivityHypothesis` term
  exists over it, and its `Nontrivial` witness is a genuine flat-vs-CURVED pair
  (`nontrivial_curved_UconfigRegPos`), not two flat gauge representatives;
* `Δ_nonconstant` is witnessed ACROSS A CURVATURE DIFFERENCE
  (`deltaKC_su2_nonconstant_of_kappa_ne` at `uRegFlat`/`uRegCurved`), which is what that field
  was meant to say;
* the coercivity field holds with an EXPLICIT `γ'' = 1/3 − a − 2⟪v0,J⟫`, no `Classical.choose`,
  no `sorry`, no free `γ` slot.

What it does NOT establish, and must not be read as: Bałaban's p.428 claim. The `Δ` used here is
the disclosed `Q = Qstar = 1` operator, whose quadratic form on `V` is a pure scalar
(`inner_deltaKC_su2_eq_scalar`); the bound holds for arbitrary `U`
(`deltaKC_su2_uniform_lower_bound`), so the regular-`U` restriction is doing NO work. The gap to
p.428 is `[LEM-Q1REAL-ADJOINT]` (operator faithfulness), and it is untouched by this instance.
`gamma_exists_su2` and `faithfulCoercivityHypothesisSU2` (§10) are deliberately left in place,
`sorry` and all, so that this file does not appear to have discharged more than it has.

**DISCLOSED FREEDOM IN `α` (S91, stated before anyone has to find it).** `α` is a caller-supplied
parameter bounded only by `0 < α`; there is NO upper bound. At `α ≥ 8` the domain
`UconfigRegPos α` is EVERY configuration
(`FaithfulDeltaKNonScalar.holonomyDefectSq_le_eight`,
`FaithfulDeltaKNonScalar.uconfigReg_vs_uconfigReg8`), i.e. the opposite degeneracy from `α = 0`.
This is NOT a soundness hole here — `deltaKC_su2_uniform_lower_bound` is proved for arbitrary `U`,
so the term is honest at every `α` — but it means the `α` in this instance CARRIES NO SMALLNESS.
No upper bound is imposed because this file has no principled value to impose: CMP99b p.428 says
only "`Mα₀` sufficiently small" and gives no number, and inventing one would be exactly the
free-constant defect this file was already convicted for. The smallness that a faithful
`Δ_k` will need is the one `uRegCurved_frobSupBond_le` measures (`α₁ ≤ √α`), and it must be
fixed by the consumer, not here. -/
noncomputable def coercivityHypothesisSU2Pos_ofGate
    (bc : BaseConstant) (v0 J : BFL2 witnessL) (_hJ : J ≠ 0)
    (RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL))
    {α : ℝ} (hα : 0 < α)
    (hgate : usedAt bc 0 + 2 * (inner ℝ v0 J : ℝ) < 1 / 3) :
    @AdalyFormal.Balaban.CoercivityHypothesis (BFL2 witnessL) (UconfigRegPos α) _ _
      (nontrivial_curved_UconfigRegPos hα) :=
  -- explicit `@…mk`, not `where`: the `Nontrivial` instance is supplied by hand
  -- (`nontrivial_curved_UconfigRegPos hα`), and structure-instance notation would try to
  -- synthesize it instead — there is deliberately NO global `Nontrivial (UconfigRegPos α)`
  -- instance, since the class is FALSE for `α < 0` (the subtype is then empty).
  @AdalyFormal.Balaban.CoercivityHypothesis.mk (BFL2 witnessL) (UconfigRegPos α) _ _
    (nontrivial_curved_UconfigRegPos hα)
    (fun _ U => deltaKC_su2 bc v0 J (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD U.val)
    (subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL))
    subspace156BFL2_ne_bot
    (by
      obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot subspace156BFL2_ne_bot
      refine ⟨0, uRegFlat hα.le, uRegCurved hα, uRegFlat_ne_uRegCurved hα, ?_⟩
      exact deltaKC_su2_nonconstant_of_kappa_ne bc v0 J Finset.univ ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD _ _
        (fun h => uRegCurved_kappa_ne hα h.symm) v (RD.retraction v hvmem) hvne)
    ((1 / 3 : ℝ) - usedAt bc 0 - 2 * (inner ℝ v0 J : ℝ))
    (by linarith)
    (fun _ U v hv => deltaKC_su2_uniform_lower_bound bc v0 J Finset.univ ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll RD U.val v (RD.retraction v hv))

#print axioms coercivityHypothesisSU2Pos_ofGate

/-- **THE CONTROL THAT THE RE-TARGETED INSTANCE IS NON-DEGENERATE.** Its configuration domain
contains a background with nonzero curvature that is not a gauge transform of ANY flat
configuration. The `α = 0` instance (`faithfulCoercivityHypothesisSU2`) provably cannot satisfy
this (`no_curved_mem_UconfigReg`) — so the two differ in exactly the way the 2026-07-26 sweep
demanded, and the difference is checkable rather than asserted. -/
theorem coercivityHypothesisSU2Pos_domain_nondegenerate {α : ℝ} (hα : 0 < α) :
    (∃ U : UconfigRegPos α, ∃ p : PeriodicLatticePlaquette witnessL,
        holonomyElem U.val p ≠ 1) ∧
      ¬ ∃ U : UconfigReg, ∃ p : PeriodicLatticePlaquette witnessL, holonomyElem U.val p ≠ 1 :=
  ⟨⟨uRegCurved hα, uRegCurved_curved hα⟩, no_curved_mem_UconfigReg⟩

#print axioms coercivityHypothesisSU2Pos_domain_nondegenerate

/-! ### §10c — TWO FURTHER INHERITED DEFECTS, MOVED FROM PROSE INTO THE KERNEL (OPS-10, 2026-07-26)

Both were already found by the de-correlated Sol gate (`compute/sol_su2_gate/SOL_VERDICT.md`) and
both still lived only in a verdict file. Neither is REPAIRED here — repairing them is a different
lane's mandate — but a defect that is a theorem cannot be forgotten the way a defect in a
`VERDICT.md` can. This lane's own finding (`UconfigReg` = the flat set) had ALSO already been
recorded by that same Sol gate ("`UconfigReg` at threshold zero is a flat-holonomy proxy, not
CMP99b (3.35)/(3.36)", §(a)) and was not propagated into the file for three days. -/

/-- **THE `_hJ : J ≠ 0` GUARD IS DEFEATED BY `v0 := 0`.** The source correction vanishes
identically, exactly as it does at `J = 0`, so the guard advertised in §11 as excluding "the
historical `J=0` collapse" excludes only that literal call, not the collapse.

**OPS-3 — how this fails.** It is false if `solutionOperator (su2CovarianceData U)` is anything
other than the identity on `0` — i.e. it rests on `map_zero`, not on the inherited `Q = Qstar = 1`
collapse; a genuinely `U`-dependent `H₁` would still send `0` to `0`, so this defect is
structural, not an artifact of the disclosed simplification. -/
theorem sourceCorrectionSU2_v0_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (J : BFL2 witnessL) : sourceCorrectionSU2 U 0 J = 0 := by
  unfold sourceCorrectionSU2
  rw [solutionOperator_su2_eq_id, inner_zero_left]
  simp

/-- **THE `k` AXIS IS INERT.** `deltaKC_su2` has no `k` argument at all, so the `Δ` field of both
`faithfulCoercivityHypothesisSU2` and `coercivityHypothesisSU2Pos_ofGate` is constant in the RG
scale, and "uniform in `k`" — the whole point of CMP96 p.244's `γ₀''` and of CMP99b p.428's
"independent of `k` and `U`" — is satisfied for free. Stated as a theorem so that the
`∀ k` in `coercive` is never read as carrying content.

**OPS-3 — how this fails.** It is `rfl`, hence unfalsifiable BY CONSTRUCTION — which is precisely
the disclosure: a `∀ k` over a `k`-constant family is not a check, and no mutation of the
mathematics could make this statement fail. It is recorded as evidence ABOUT the construction,
never as evidence FOR it. -/
theorem coercivityHypothesisSU2Pos_Delta_k_independent
    (bc : BaseConstant) (v0 J : BFL2 witnessL) (hJ : J ≠ 0)
    (RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL))
    {α : ℝ} (hα : 0 < α)
    (hgate : usedAt bc 0 + 2 * (inner ℝ v0 J : ℝ) < 1 / 3)
    (k k' : ℕ) (U : UconfigRegPos α) :
    @AdalyFormal.Balaban.CoercivityHypothesis.Δ (BFL2 witnessL) (UconfigRegPos α) _ _
        (nontrivial_curved_UconfigRegPos hα)
        (coercivityHypothesisSU2Pos_ofGate bc v0 J hJ RD hα hgate) k U =
      @AdalyFormal.Balaban.CoercivityHypothesis.Δ (BFL2 witnessL) (UconfigRegPos α) _ _
        (nontrivial_curved_UconfigRegPos hα)
        (coercivityHypothesisSU2Pos_ofGate bc v0 J hJ RD hα hgate) k' U := rfl

#print axioms sourceCorrectionSU2_v0_zero
#print axioms coercivityHypothesisSU2Pos_Delta_k_independent

/-! ## §11 — JUNK-INHABITATION AUDIT (S91/OPS-3): every historical degenerate collapse checked
against THIS file's own construction -/

/-- **`J := 0` cannot even be supplied** — `faithfulCoercivityHypothesisSU2`'s own signature
requires `_hJ : J ≠ 0`; `J := 0` fails to typecheck a call, not merely produces a weaker bound.
⚠ **TRUE BUT INEFFECTIVE (disclosed 2026-07-26, `sourceCorrectionSU2_v0_zero` §11b): the guard
does not achieve what it is for.** `v0 := 0` with `J ≠ 0` passes it and produces the SAME zero
source correction. This was already found by the de-correlated Sol gate
(`compute/sol_su2_gate/SOL_VERDICT.md` §(b), compiled probe) and is only now in the kernel. -/
example (bc : BaseConstant) (v0 : BFL2 witnessL)
    (RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)) :
    True := by
  -- `faithfulCoercivityHypothesisSU2 bc v0 0 (h : (0:BFL2 witnessL) ≠ 0) RD` has NO proof of
  -- `h` (`ne_self_iff_false`), so no such call exists — the historical `J=0` collapse
  -- (`lem_coerc_u1_deltaK`'s conviction) is excluded at the SIGNATURE level.
  trivial

/-- **`RD.C := 0` and `RD.C := id` are BOTH structurally excluded** — `reparamDataSU2_blocks_zero`
(needs the `V ≠ ⊥` witness, at the fixed instantiation) and `reparamDataSU2_blocks_id` (needs
`V ≠ ⊤`, general in `U`) restated here as the audit's own summary. -/
theorem junk_audit_reparamC :
    (¬ ∃ RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        RD.C = (0 : BFL2 witnessL →L[ℝ] BFL2 witnessL)) ∧
    (¬ ∃ RD : ReparamDataSU2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL),
        RD.C = (1 : BFL2 witnessL →L[ℝ] BFL2 witnessL)) :=
  ⟨reparamDataSU2_blocks_zero,
    reparamDataSU2_blocks_id (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅
      AdalyFormal.Balaban.AdmissibleSubspace.witnessEll (trivialU witnessL)⟩

#print axioms junk_audit_reparamC

/-- **`V := ⊥` is BLOCKED STRUCTURALLY** — every term of `CoercivityHypothesis` carries
`V_ne_bot` intrinsically (`Coercivity.lean`'s own R3 correction, inherited unchanged). -/
theorem junk_audit_V_ne_bot {Uc : Type*} [Nontrivial Uc]
    (h : AdalyFormal.Balaban.CoercivityHypothesis (BFL2 witnessL) Uc) : h.V ≠ ⊥ := h.V_ne_bot

#print axioms junk_audit_V_ne_bot

/-! **The stage-1 `γ0`-free-choice exploit is NOT EXPRESSIBLE against this file's constructor.**
`faithfulCoercivityHypothesisSU2`'s signature (`bc`,`v0`,`J`,`_hJ`,`RD`) carries NO `γ0`/`hγ0`
argument for a caller to instantiate adversarially — `γ''` is bound entirely inside
`gamma_exists_su2`'s own existential, never supplied externally. This is a signature-level fact,
recorded here as the audit's own closing note rather than as a further Lean theorem (there is no
term to falsify: the exploit requires an argument slot this constructor does not have). -/

end AdalyFormal.Balaban.FaithfulCoercivitySU2
