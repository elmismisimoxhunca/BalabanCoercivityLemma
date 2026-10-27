/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarReconciliation
import AdalyFormal.Balaban.ClassPropagationUbar
import AdalyFormal.Balaban.DeltaKSuTwoFaithful
import AdalyFormal.Balaban.LatticeFourier
import AdalyFormal.Balaban.BoundedReparam
import AdalyFormal.Balaban.IteratedAveraging
import AdalyFormal.Migration.L8Gaussian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Basis.VectorSpace
import AdalyFormal.Balaban.Claim18Repaired
import AdalyFormal.Balaban.LastLayerNoGo
import AdalyFormal.Balaban.CoercUMainKernel
import AdalyFormal.Balaban.CoercUMainDesigned

set_option autoImplicit false
set_option maxRecDepth 40000

/-!
# THE PER-STEP BLOCKING RATE IS AT LEAST `19/4`, AND `R2` IS FALSE

Lane record: `compute/r2_blkrate/PROGRESS.md`.

## §0 — WHAT IS DECIDED HERE

`GoalRegister.R2_BlockingRateBelowPrescaling` asks whether the tree's pinned blocking map grows
`frobSupBond` by at most the source's own pre-scaling rate `L² = 4`:

    ∀ L V,  frobSupBond (ubarCoarse 2 V)  ≤  4 · frobSupBond V .

`ClassPropagationUbar` brackets the true constant by `2 ≤ C_blk ≤ 2 + 5π` and `4` sits strictly
inside that bracket, so the bracket does not decide it. **It is decided here, in the negative.**

* `blocking_rate_ge_19_4` — for EVERY `c < 19/4` the claim "blocking multiplies `frobSupBond` by at
  most `c`" is FALSE, already on a single `4×4×4` periodic lattice. This replaces the tree's
  `no_contraction_ubarCoarse` lower end `2` by `19/4`, so the sandwich becomes

      19/4  ≤  C_blk  ≤  2 + 5π .

* `R2_BlockingRateBelowPrescaling_false` — since `4 < 19/4`, `R2` is refuted.
* `prescaling_budget_deficit` — every constant up to and INCLUDING the source's own per-level
  pre-scaling rate `L² = 4` is refuted. (The gap `19/4 − 4 = 3/4` is arithmetic on two numerals
  and is deliberately NOT stated as a theorem; see that declaration's own docstring.)
* `prescaling_does_not_absorb` — hence the source's depth-known-in-advance schedule
  `α₀ ↦ 4^{-n}·α₀` does NOT absorb this map's growth: a budget propagated at the proved
one-step worst-case rate leaves `(19/16)ⁿ·a` [S75 2026-08-02, main loop, Sol gate F1: the
theorem `prescaling_does_not_absorb` is ARITHMETIC over reals -- no orbit of `ubarCoarse` is
proved to realize the product of one-step worst cases at every scale; extremizers may change
per level. The original sentence read "the level-n radius is (19/16)^n a", an iterated-orbit
overclaim],
  which exceeds every target at some depth.

## §1 — HOW THE CONSTANT IS FOUND, AND WHICH DIRECTION THE SECTOR RESTRICTION CUTS

The witness lies in a **maximal torus** of `SU(2)` (`SuTwoLogExp.torus`), the one-parameter
subgroup `diag(e^{iθ}, e^{-iθ})`. On configurations valued there the ENTIRE blocking map is
**exactly affine in the bond angles** — not to first order, exactly — because `torus_add` is an
identity, `su2Log (torus θ) = θ • J` on the principal branch, and `su2Exp (θ • J) = torus θ`. So
the blocked bond angle is a fixed rational linear functional of the fine bond angles
(`ubarSU2_torusCfg`), and its `ℓ¹` norm is the sharp growth constant of the map restricted to that
sector.

**Direction of the restriction, stated explicitly.** A torus-valued configuration IS a
configuration. So the sector constant bounds the GENERAL constant **from below**, and a `> 4`
result in the sector is a genuine deficit for the general claim. Nothing here bounds the general
constant from above, and `19/4` is NOT claimed sharp for the general map — the upper end of the
sandwich is still `ClassPropagationUbar.blkConst = 2 + 5π`.

**What was computed, and where the `19/4` comes from.** The coarse bond direction is `μ = 2`, the
axis `coarseGammaPath` traverses FIRST. The `ℓ¹` mass splits as `2` from the coarse bond's own
two-fold telescoping plus `11/4` from the block-averaged staircase difference
`Γ̄_{c₋,x} − Γ̄_{c₊,x(c)}`, whose leading bond `(c₋, 2)` is shared by the four block sites with
`δ₂ = 1` and therefore carries STAIRCASE-DIFFERENCE share `4/8` [S75 2026-08-02, main loop,
Kimi gate §8(a): its TOTAL loop-average coefficient is `5/8` (an extra `1/8` from the ell-bond
leg at the origin site), `13/8` including the coarse-bond term; the original said "carries
weight 4/8" unqualified], REINFORCING (not cancelling) the coarse bond there. [S75 same date,
Sol gate F3: `2 + 11/4` is the middle-only l1 mass plus the INCREMENT of the combined mass over
it -- the raw staircase-difference vector alone has l1 mass 3; overlap makes l1 non-additive.]
The direction matters and is part of the finding: the same computation at `μ = 0` — the axis the
staircase traverses LAST — gives `ℓ¹` mass exactly `4`, and at `μ = 1` gives `9/2`. Only `μ = 2`
is formalised below; the other two are exploratory python and are asserted nowhere.

## §2 — SCOPE

* One lattice, `L = (3,3,3)` i.e. `4×4×4` sites, is enough: `R2` is a `∀ L` statement.
  The wrap-around matters — the same construction on a `2×2×2` torus gives `ℓ¹` mass `2`, because
  `c₋ + 2e₂ = c₋` there and the staircase difference cancels identically. `4` sites per axis is the
  smallest extent on which `c₋`, `c₋+e₂`, `c₋+2e₂`, `c₋+3e₂` are four distinct sites.
* `ell = 2`, stride `1`, `𝔰𝔲(2)`, periodic torus — `PerturbationRoute`'s standing scope, unchanged.
* `frobSupBond` is the tree's global bond sup. `GoalRegister` §2.1 already bills that functional as
  OURS and not the source's plaquette-holonomy regularity; this module does not change that, and
  `R2_PlaquetteGrowthContract` is untouched.
-/

namespace AdalyFormal.Balaban.AbelianBlockingRate

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp torus torus_add torus_zero coe_torus
  torusM su2J psiR su2Exp_psiR su2Log_torus)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarCoarse ubarSU2_eq_blockedLink diagSU2
  coe_diagSU2 frobSq_diagSU2_pow zc)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent blockedLink su2Of)

variable {L : PeriodicLatticeExtent}

/-! ## §3 — THE TORUS IS THE `diagSU2` FAMILY (bridge to the existing norm formulas) -/

/-- The two one-parameter families the tree carries are the same element. `SuTwoLogExpTorus` owns
the `log`/`exp` calculus, `BlockedBackground` owns the Frobenius-norm formulas; this identifies them
so neither is rebuilt (LAW-19). -/
theorem torus_eq_diagSU2 (φ : ℝ) : torus φ = diagSU2 φ := by
  apply Subtype.ext
  rw [coe_torus, coe_diagSU2, torusM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.SuTwoLogExp.dg, su2Of, zc, Matrix.diagonal,
      (AdalyFormal.Balaban.SuTwoLogExp.cexp_star φ).symm]

/-- `‖torus θ − 1‖_F = √(4(1 − cos θ))`, for every real `θ`. -/
theorem frobNorm_torus_sub_one (φ : ℝ) :
    frobNorm ((torus φ : M2) - 1) = Real.sqrt (4 * (1 - Real.cos φ)) := by
  rw [torus_eq_diagSU2]
  have h := frobSq_diagSU2_pow φ 1
  rw [pow_one, Nat.cast_one, one_mul] at h
  unfold frobNorm
  rw [h]

theorem torus_inv (t : ℝ) : (torus t)⁻¹ = torus (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← torus_add]
  simp

/-! ## §4 — THE EXACT ABELIAN TRANSFER

Every object in the blocking chain, evaluated on a torus-valued configuration, is `torus` of an
explicit REAL angle. Nothing here is an approximation. -/

/-- A configuration with all bond variables on one maximal torus, given by its angle field. -/
noncomputable def torusCfg (f : PeriodicLatticeEdge L → ℝ) : PeriodicLinkConfiguration SU2 L :=
  fun b => torus (f b)

/-- The additive analogue of `coarsePathHolonomy`: the sum of the angle field along a forward
path. Same recursion, same stride bookkeeping. -/
def pathAngle (s : ℕ) (f : PeriodicLatticeEdge L → ℝ) :
    PeriodicLatticeSite L → List (Fin 3) → ℝ
  | _, [] => 0
  | y, μ :: rest => f (y, μ) + pathAngle s f (coarseShift y s μ) rest

@[simp] theorem pathAngle_nil (s : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (y : PeriodicLatticeSite L) : pathAngle s f y [] = 0 := rfl

@[simp] theorem pathAngle_cons (s : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (rest : List (Fin 3)) :
    pathAngle s f y (μ :: rest) = f (y, μ) + pathAngle s f (coarseShift y s μ) rest := rfl

/-- **Transfer, leg 1: holonomy of a torus configuration is `torus` of the path angle.** -/
theorem coarsePathHolonomy_torusCfg (s : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (y : PeriodicLatticeSite L) (P : List (Fin 3)) :
    coarsePathHolonomy s (torusCfg f) y P = torus (pathAngle s f y P) := by
  induction P generalizing y with
  | nil => exact torus_zero.symm
  | cons μ rest ih =>
      show (torusCfg f) (y, μ) * coarsePathHolonomy s (torusCfg f) (coarseShift y s μ) rest = _
      rw [ih, pathAngle_cons, torus_add]
      rfl

/-- The angle of the coarse bond variable: `ell` fine bonds along `c.2`. -/
def bondAngle (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ) (c : PeriodicLatticeEdge L) : ℝ :=
  pathAngle s f c.1 (List.replicate ell c.2)

/-- The angle of the closed loop `W_x = V(Γ_{c,x})·V(c)⁻¹`: staircase, `ell`-fold bond, minus the
translated staircase, minus the coarse bond. -/
def loopAngle (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) : ℝ :=
  pathAngle s f c.1 (coarseGammaPath s c.1 x) + pathAngle s f x (List.replicate ell c.2)
    - pathAngle s f (cPlusS s ell c) (coarseGammaPath s c.1 x) - bondAngle s ell f c

theorem coarseBondVar_torusCfg (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) :
    coarseBondVar s ell (torusCfg f) c = torus (bondAngle s ell f c) :=
  coarsePathHolonomy_torusCfg s f c.1 _

theorem loopVar_torusCfg (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    loopVar s ell (torusCfg f) c x = torus (loopAngle s ell f c x) := by
  show gammaVarStrided s ell (torusCfg f) c x * (coarseBondVar s ell (torusCfg f) c)⁻¹ = _
  unfold gammaVarStrided
  rw [coarsePathHolonomy_torusCfg, coarsePathHolonomy_torusCfg, coarsePathHolonomy_torusCfg,
    coarseBondVar_torusCfg, torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  congr 1

/-- **The blocked bond angle** — the linear functional whose `ℓ¹` norm is the sector-sharp
per-step growth constant. -/
noncomputable def blkAngle (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) : ℝ :=
  (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * loopAngle s ell f c x) + bondAngle s ell f c

/-- **THE TRANSFER THEOREM.** On a torus-valued configuration whose block loop angles all lie in
the principal branch `[0, π)`, the pinned blocking map is EXACTLY `torus ∘ blkAngle` — an affine
map on angles, with no error term. -/
theorem ubarSU2_torusCfg (s ell : ℕ) (f : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L)
    (hbr : ∀ x ∈ stepBlockOf c.1 s ell, 0 ≤ loopAngle s ell f c x ∧
      loopAngle s ell f c x < Real.pi) :
    ubarSU2 s ell (torusCfg f) c = torus (blkAngle s ell f c) := by
  rw [ubarSU2_eq_blockedLink]
  show su2Exp (blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg f) c x)) * coarseBondVar s ell (torusCfg f) c = _
  have hexp : blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg f) c x)
      = psiR (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * loopAngle s ell f c x) := by
    unfold blockExponent psiR
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp only
    rw [loopVar_torusCfg, su2Log_torus (hbr x hx).1 (hbr x hx).2]
    unfold psiR
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [hexp, su2Exp_psiR, coarseBondVar_torusCfg, ← torus_add, blkAngle]

/-! ## §5 — THE WITNESS LATTICE, THE WITNESS CONFIGURATION, AND ITS BLOCKED ANGLE -/

/-- `4 × 4 × 4` periodic sites. Four per axis is the smallest extent on which `c₋`, `c₋+e₂`,
`c₋+2e₂`, `c₋+3e₂` are four DISTINCT sites, which is exactly what the staircase difference needs;
on a `2×2×2` torus it cancels identically. `2 ∣ 4`, so the coarse extent is honest. -/
abbrev LW : PeriodicLatticeExtent := fun _ => 3

abbrev StW := PeriodicLatticeSite LW

/-- Explicit site constructor, so every site below is a closed term. -/
def st (a b c : Fin 4) : StW := ![a, b, c]

@[simp] theorem st_zero (a b c : Fin 4) : st a b c 0 = a := rfl
@[simp] theorem st_one (a b c : Fin 4) : st a b c 1 = b := rfl
@[simp] theorem st_two (a b c : Fin 4) : st a b c 2 = c := rfl

@[simp] theorem shift_st_0 (a b c : Fin 4) : coarseShift (st a b c) 1 0 = st (a + 1) b c := by
  funext μ
  rw [coarseShift, Function.iterate_one]
  fin_cases μ <;> simp [st, AdalyFormal.Target.ClayStatement.periodicLatticeShift]

@[simp] theorem shift_st_1 (a b c : Fin 4) : coarseShift (st a b c) 1 1 = st a (b + 1) c := by
  funext μ
  rw [coarseShift, Function.iterate_one]
  fin_cases μ <;> simp [st, AdalyFormal.Target.ClayStatement.periodicLatticeShift]

@[simp] theorem shift_st_2 (a b c : Fin 4) : coarseShift (st a b c) 1 2 = st a b (c + 1) := by
  funext μ
  rw [coarseShift, Function.iterate_one]
  fin_cases μ <;> simp [st, AdalyFormal.Target.ClayStatement.periodicLatticeShift]

/-- The coarse bond under test: based at the origin, in direction `2` — the axis
`coarseGammaPath` traverses FIRST. -/
def cW : PeriodicLatticeEdge LW := (st 0 0 0, 2)

/-- The sign pattern of the witness. `true` marks the bonds carrying `−ε`. It is the sign of the
blocked-angle coefficient at each bond, so that every one of the 24 bonds in the support
contributes `|coefficient|·ε` with no cancellation. `Bool`-valued, hence `decide`-evaluable at
every closed bond. -/
def negBond (b : PeriodicLatticeEdge LW) : Bool :=
  if b.2 = 2 then decide (b.1 = st 0 0 2) else decide (2 ≤ (b.1 2).val)

/-- **THE WITNESS ANGLE FIELD.** Every bond carries angle `±ε`; which sign is fixed by
`negBond`. Nothing here is fitted to a target: the sign pattern is read off the coefficient
vector, and `ε` is left free. -/
def fW (e : ℝ) (b : PeriodicLatticeEdge LW) : ℝ := if negBond b then -e else e

/-- **THE WITNESS CONFIGURATION.** -/
noncomputable def VW (e : ℝ) : PeriodicLinkConfiguration SU2 LW := torusCfg (fW e)

theorem fW_pos {b : PeriodicLatticeEdge LW} (e : ℝ) (h : negBond b = false) : fW e b = e := by
  simp [fW, h]

theorem fW_neg {b : PeriodicLatticeEdge LW} (e : ℝ) (h : negBond b = true) : fW e b = -e := by
  simp [fW, h]

/-- **THE BLOCK, ENUMERATED.** `B₁(c₋)` at `ell = 2` is the `2×2×2` corner cube; kernel-checked. -/
theorem block_eq : stepBlockOf cW.1 1 2
    = ({st 0 0 0, st 0 0 1, st 0 1 0, st 0 1 1,
        st 1 0 0, st 1 0 1, st 1 1 0, st 1 1 1} : Finset StW) := by
  decide

theorem cPlus_eq : cPlusS 1 2 cW = st 0 0 2 := by decide

theorem replicate_two : List.replicate 2 cW.2 = [(2 : Fin 3), 2] := by decide

theorem gamma_000 : coarseGammaPath 1 cW.1 (st 0 0 0) = [] := by decide
theorem gamma_001 : coarseGammaPath 1 cW.1 (st 0 0 1) = [2] := by decide
theorem gamma_010 : coarseGammaPath 1 cW.1 (st 0 1 0) = [1] := by decide
theorem gamma_011 : coarseGammaPath 1 cW.1 (st 0 1 1) = [2, 1] := by decide
theorem gamma_100 : coarseGammaPath 1 cW.1 (st 1 0 0) = [0] := by decide
theorem gamma_101 : coarseGammaPath 1 cW.1 (st 1 0 1) = [2, 0] := by decide
theorem gamma_110 : coarseGammaPath 1 cW.1 (st 1 1 0) = [1, 0] := by decide
theorem gamma_111 : coarseGammaPath 1 cW.1 (st 1 1 1) = [2, 1, 0] := by decide

/-! ### §5a — the eight block loop angles, each an exact multiple of `ε`

Every one of the eight is computed, none is estimated. `loopAngle` at the base point `c₋` is `0` on
the nose — the loop there is the coarse bond against itself — which is the structural reason the
block average cannot be replaced by its worst term. -/

theorem loop_000 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 0 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [gamma_000, cPlus_eq, replicate_two]
  simp +decide [fW, st]

theorem loop_001 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 0 0 1) = 0 := by
  unfold loopAngle bondAngle
  rw [gamma_001, cPlus_eq, replicate_two]
  simp +decide [fW, st]

theorem loop_010 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 0 1 0) = 2 * e := by
  unfold loopAngle bondAngle
  rw [gamma_010, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem loop_011 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 0 1 1) = 4 * e := by
  unfold loopAngle bondAngle
  rw [gamma_011, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem loop_100 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 1 0 0) = 2 * e := by
  unfold loopAngle bondAngle
  rw [gamma_100, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem loop_101 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 1 0 1) = 4 * e := by
  unfold loopAngle bondAngle
  rw [gamma_101, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem loop_110 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 1 1 0) = 4 * e := by
  unfold loopAngle bondAngle
  rw [gamma_110, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem loop_111 (e : ℝ) : loopAngle 1 2 (fW e) cW (st 1 1 1) = 6 * e := by
  unfold loopAngle bondAngle
  rw [gamma_111, cPlus_eq, replicate_two]
  simp +decide [fW, st]
  ring

theorem bondAngle_cW (e : ℝ) : bondAngle 1 2 (fW e) cW = 2 * e := by
  unfold bondAngle
  rw [replicate_two]
  simp +decide [fW]
  ring

/-! ### §5b — the blocked angle: `19/4 · ε`, exactly

`(1/8)·(0+0+2+4+2+4+4+6)·ε + 2·ε = (11/4 + 2)·ε = (19/4)·ε`. The `2` is the coarse bond's own
two-fold telescoping; the `11/4` is the block-averaged staircase difference. Both are counted, not
fitted, and `ε` is free. -/
theorem blkAngle_cW (e : ℝ) : blkAngle 1 2 (fW e) cW = 19 / 4 * e := by
  unfold blkAngle
  rw [block_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_000, loop_001, loop_010, loop_011, loop_100, loop_101, loop_110, loop_111, bondAngle_cW]
  norm_num
  ring

/-- Every block loop angle sits in the principal branch `[0, π)` as soon as `0 ≤ ε` and `6ε < π`.
The largest of the eight is `6ε`, at the far corner of the block. -/
theorem loop_branch {e : ℝ} (he : 0 ≤ e) (he6 : 6 * e < Real.pi) :
    ∀ x ∈ stepBlockOf cW.1 1 2,
      0 ≤ loopAngle 1 2 (fW e) cW x ∧ loopAngle 1 2 (fW e) cW x < Real.pi := by
  intro x hx
  rw [block_eq] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_000, loop_001, loop_010, loop_011, loop_100, loop_101, loop_110,
      loop_111] <;> exact ⟨by linarith, by linarith⟩

/-- **THE BLOCKED BOND, EVALUATED.** One blocking step sends the witness to `torus ((19/4)·ε)` at
the bond `cW`. Exact; no estimate anywhere in the chain. -/
theorem ubarSU2_VW {e : ℝ} (he : 0 ≤ e) (he6 : 6 * e < Real.pi) :
    ubarSU2 1 2 (VW e) cW = torus (19 / 4 * e) := by
  rw [VW, ubarSU2_torusCfg 1 2 (fW e) cW (loop_branch he he6), blkAngle_cW]

/-! ## §6 — THE TWO FROBENIUS NORMS, AND THE REFUTATION -/

theorem four_one_sub_cos (θ : ℝ) : 4 * (1 - Real.cos θ) = 8 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  have hs := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [h, hs]

theorem sqrt_four_one_sub_cos (θ : ℝ) :
    Real.sqrt (4 * (1 - Real.cos θ)) = Real.sqrt 8 * |Real.sin (θ / 2)| := by
  rw [four_one_sub_cos, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_sq_eq_abs]

/-- Every bond of the witness has the SAME deviation: the sign pattern only moves the angle's
sign, and `cos` is even. -/
theorem frobNorm_VW (e : ℝ) (b : PeriodicLatticeEdge LW) :
    frobNorm ((VW e b : M2) - 1) = Real.sqrt (4 * (1 - Real.cos e)) := by
  show frobNorm ((torus (fW e b) : M2) - 1) = _
  rw [frobNorm_torus_sub_one]
  cases hb : negBond b <;> simp [fW, hb, Real.cos_neg]

theorem frobSupBond_VW (e : ℝ) : frobSupBond (VW e) = Real.sqrt (4 * (1 - Real.cos e)) := by
  unfold frobSupBond
  rw [show (fun b : AdalyFormal.Balaban.AdmissibleSubspace.Bond LW =>
      frobNorm ((VW e b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
      = fun _ => Real.sqrt (4 * (1 - Real.cos e)) from funext (fun b => frobNorm_VW e b)]
  exact Finset.sup'_const _ _

/-- The coarse bond at which the blocked configuration is read: the origin of the coarse lattice,
direction `2`. Its `toFine` image is `cW.1` on the nose. -/
def cCoarse : PeriodicLatticeEdge (AdalyFormal.Balaban.U1AnchorCoarse.coarseExtent LW 2) := (0, 2)

theorem ubarCoarse_VW_at {e : ℝ} (he : 0 ≤ e) (he6 : 6 * e < Real.pi) :
    ubarCoarse 2 (VW e) cCoarse = torus (19 / 4 * e) := by
  show ubarSU2 1 2 (VW e)
    (AdalyFormal.Balaban.U1AnchorCoarse.toFine LW 2 cCoarse.1, cCoarse.2) = _
  rw [show (AdalyFormal.Balaban.U1AnchorCoarse.toFine LW 2 cCoarse.1, cCoarse.2) = cW from by
    decide]
  exact ubarSU2_VW he he6

theorem frobSupBond_ubarCoarse_VW_ge {e : ℝ} (he : 0 ≤ e) (he6 : 6 * e < Real.pi) :
    Real.sqrt (4 * (1 - Real.cos (19 / 4 * e))) ≤ frobSupBond (ubarCoarse 2 (VW e)) := by
  have h := frobNorm_le_frobSupBond (ubarCoarse 2 (VW e)) cCoarse
  rwa [ubarCoarse_VW_at he he6, frobNorm_torus_sub_one] at h

/-- **THE STRICT COMPARISON.** For `0 < c < 19/4`, the witness at
`ε = min (8/19) ((19/4 − c)/10)` already breaks the constant `c`. The two elementary sine bounds
`sin x < x` and `x − x³/4 < sin x` are all that is used; the choice of `ε` is explicit and the
verification is rational arithmetic. -/
theorem strict_comparison {c e : ℝ} (hc0 : 0 < c) (hc : c < 19 / 4) (he : 0 < e)
    (he8 : e ≤ 8 / 19) (hed : e ≤ (19 / 4 - c) / 10) :
    c * Real.sqrt (4 * (1 - Real.cos e)) < Real.sqrt (4 * (1 - Real.cos (19 / 4 * e))) := by
  have hd : 0 < 19 / 4 - c := by linarith
  have hhalf : (19 / 4 * e) / 2 = 19 * e / 8 := by ring
  rw [sqrt_four_one_sub_cos, sqrt_four_one_sub_cos, hhalf]
  have hs8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hx1 : (0 : ℝ) < 19 * e / 8 := by linarith
  have hx2 : 19 * e / 8 ≤ 1 := by linarith
  have hsinbig : 19 * e / 8 - (19 * e / 8) ^ 3 / 4 < Real.sin (19 * e / 8) :=
    Real.sin_gt_sub_cube hx1 hx2
  have hsinsmall : Real.sin (e / 2) < e / 2 := Real.sin_lt (by linarith)
  have hsinsmall0 : 0 < Real.sin (e / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_gt_three])
  have hsinbig0 : 0 < Real.sin (19 * e / 8) :=
    Real.sin_pos_of_pos_of_lt_pi hx1 (by nlinarith [Real.pi_gt_three])
  rw [abs_of_pos hsinsmall0, abs_of_pos hsinbig0]
  -- the cubic budget: e² ≤ (d/10)·(8/19) is enough
  have hee : e * e ≤ ((19 / 4 - c) / 10) * (8 / 19) :=
    mul_le_mul hed he8 (le_of_lt he) (by linarith)
  have hkey : c * (e / 2) ≤ 19 * e / 8 - (19 * e / 8) ^ 3 / 4 := by nlinarith [hee, he, hd]
  have h1 : c * Real.sin (e / 2) < c * (e / 2) := mul_lt_mul_of_pos_left hsinsmall hc0
  have hchain : c * Real.sin (e / 2) < Real.sin (19 * e / 8) := by linarith
  calc c * (Real.sqrt 8 * Real.sin (e / 2))
      = Real.sqrt 8 * (c * Real.sin (e / 2)) := by ring
    _ < Real.sqrt 8 * Real.sin (19 * e / 8) := mul_lt_mul_of_pos_left hchain hs8

/-- **THE LOWER END OF THE SANDWICH, RAISED FROM `2` TO `19/4`.** For EVERY `c < 19/4` the claim
"one blocking step multiplies `frobSupBond` by at most `c`" is FALSE — on the single `4×4×4`
periodic lattice `LW`, with a witness constructed from `c` inside the proof (S91: nothing
existential is handed to the prover).

This strengthens `ClassPropagationUbar.no_contraction_ubarCoarse`, whose lower end was `2`. -/
theorem blocking_rate_ge_19_4 {c : ℝ} (hc : c < 19 / 4) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 LW,
        frobSupBond (ubarCoarse 2 V) ≤ c * frobSupBond V) := by
  intro hall
  -- replace `c` by `max c 1`, so the sine estimate may assume positivity
  set c' : ℝ := max c 1 with hc'
  have hc'pos : 0 < c' := lt_of_lt_of_le one_pos (le_max_right c 1)
  have hc'lt : c' < 19 / 4 := max_lt hc (by norm_num)
  have hall' : ∀ V : PeriodicLinkConfiguration SU2 LW,
      frobSupBond (ubarCoarse 2 V) ≤ c' * frobSupBond V := fun V =>
    le_trans (hall V) (mul_le_mul_of_nonneg_right (le_max_left c 1) (frobSupBond_nonneg V))
  set e : ℝ := min (8 / 19) ((19 / 4 - c') / 10) with he'
  have hd : 0 < 19 / 4 - c' := by linarith
  have he0 : 0 < e := lt_min (by norm_num) (by linarith)
  have he8 : e ≤ 8 / 19 := min_le_left _ _
  have hed : e ≤ (19 / 4 - c') / 10 := min_le_right _ _
  have he6 : 6 * e < Real.pi := by nlinarith [Real.pi_gt_three]
  have hlow := frobSupBond_ubarCoarse_VW_ge (le_of_lt he0) he6
  have hup := hall' (VW e)
  rw [frobSupBond_VW] at hup
  have := strict_comparison hc'pos hc'lt he0 he8 hed
  linarith

/-- No UNIFORM constant below `19/4` works either — the same refutation, read against the
`∀ L` form the register item actually uses. -/
theorem no_uniform_constant_below_19_4 {c : ℝ} (hc : c < 19 / 4) :
    ¬ (∀ (L : PeriodicLatticeExtent) (V : PeriodicLinkConfiguration SU2 L),
        frobSupBond (ubarCoarse 2 V) ≤ c * frobSupBond V) := fun h =>
  blocking_rate_ge_19_4 hc (fun V => h LW V)

/-- **THE SANDWICH.** `19/4 ≤ C_blk ≤ 2 + 5π`, the upper end consumed from
`ClassPropagationUbar` rather than restated (LAW-19). -/
theorem blocking_rate_sandwich (V : PeriodicLinkConfiguration SU2 LW) :
    frobSupBond (ubarCoarse 2 V)
        ≤ AdalyFormal.Balaban.ClassPropagationUbar.blkConst * frobSupBond V
      ∧ ∀ c : ℝ, c < 19 / 4 → ¬ (∀ W : PeriodicLinkConfiguration SU2 LW,
          frobSupBond (ubarCoarse 2 W) ≤ c * frobSupBond W) :=
  ⟨AdalyFormal.Balaban.ClassPropagationUbar.frobSupBond_ubarCoarse_le_two V,
    fun _ hc => blocking_rate_ge_19_4 hc⟩

/-- **THE DEFICIT AGAINST THE PRE-SCALING BUDGET.** Every constant up to and INCLUDING the source's
own per-level pre-scaling rate `L² = 4` is refuted.

**A first draft of this theorem carried a second conjunct `(4:ℝ) + 3/4 = 19/4`. It is removed: it is
`norm_num`-level numeral bookkeeping, it asserts nothing about the blocking map, and a decorative
conjunct inside a substantive theorem is exactly the shape that gets miscounted as a check.** The
gap between the refuted budget `4` and the proved threshold `19/4` is `3/4` by arithmetic on two
numerals; that sentence is commentary, and it is not restated as a theorem anywhere in this file. -/
theorem prescaling_budget_deficit (c : ℝ) (hc : c ≤ 4) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 LW,
        frobSupBond (ubarCoarse 2 V) ≤ c * frobSupBond V) :=
  blocking_rate_ge_19_4 (by linarith)

/-- **AND THE PRE-SCALING SCHEDULE THEREFORE DOES NOT ABSORB THE GROWTH.** `R2_implies_depthUniform`
pre-divides the level-`0` radius by `4ⁿ` and needs a per-step factor `≤ 4`. At the proved rate the
budget propagated at the proved one-step worst-case rate is `(19/16)ⁿ·a` [S75 2026-08-02:
arithmetic statement, not a proved orbit -- see header note], unbounded in `n`: for every target `M` some depth
exceeds it. The residual per-level factor is `19/16 > 1`. -/
theorem prescaling_does_not_absorb {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ n : ℕ, M < (19 / 4 : ℝ) ^ n * (a / 4 ^ n) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / a) (by norm_num : (1 : ℝ) < 19 / 16)
  refine ⟨n, ?_⟩
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hrw : (19 / 4 : ℝ) ^ n * (a / 4 ^ n) = (19 / 16 : ℝ) ^ n * a := by
    rw [div_pow, div_pow, show (16 : ℝ) ^ n = 4 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
    field_simp
  rw [hrw]
  have : M / a * a < (19 / 16 : ℝ) ^ n * a := by
    exact mul_lt_mul_of_pos_right hn ha
  rwa [div_mul_cancel₀ _ (ne_of_gt ha)] at this

/-- **CONTROL — the witness is not degenerate.** Its bond deviation is strictly positive for
`0 < ε < π`, so the refutation is not a `frobSupBond = 0` artefact and the two sides of the broken
inequality are both nonzero. -/
theorem frobSupBond_VW_pos {e : ℝ} (he : 0 < e) (hpi : e < Real.pi) : 0 < frobSupBond (VW e) := by
  rw [frobSupBond_VW, sqrt_four_one_sub_cos]
  have h1 : 0 < Real.sin (e / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8)
  rw [abs_of_pos h1]
  positivity

/-! ## §7 — CONTROLS: this is NOT the tree's existing flat-witness phenomenon -/

/-- **The witness carries curvature.** The `(1,2)`-plaquette based at `(0,0,1)` has holonomy
`torus (2ε)`. This matters: `ClassPropagationUbar`'s refutation runs on `constU`, whose plaquette
holonomies are IDENTICALLY `1` (`holonomyElem_constU`), and on that family the exact ratio is
`√(2(1+t)) < 2` (`BlockedBackground.blocking_ratio_two`) — so no flat configuration can produce a
rate above `2`, let alone `19/4`. The mechanism here is genuinely the curvature term. -/
theorem holonomy_witness (e : ℝ) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (VW e)
      (st 0 0 1, ⟨(1, 2), by decide⟩) = torus (2 * e) := by
  show (VW e) (st 0 0 1, 1) * (VW e) (periodicLatticeShift (st 0 0 1) 1, 2)
    * ((VW e) (periodicLatticeShift (st 0 0 1) 2, 1))⁻¹ * ((VW e) (st 0 0 1, 2))⁻¹ = _
  rw [show periodicLatticeShift (st 0 0 1) 1 = st 0 1 1 from by decide,
    show periodicLatticeShift (st 0 0 1) 2 = st 0 0 2 from by decide]
  show torus _ * torus _ * (torus _)⁻¹ * (torus _)⁻¹ = _
  rw [torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  congr 1
  simp +decide [fW]
  ring

/-- The same plaquette holonomy is NOT the identity for `0 < ε` with `2ε < π`: the witness is
non-flat, so the refutation cannot be attributed to the zero-curvature sub-family on which the
tree's earlier refutation lives. -/
theorem witness_has_curvature {e : ℝ} (he : 0 < e) (hpi : 2 * e < Real.pi) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (VW e)
      (st 0 0 1, ⟨(1, 2), by decide⟩) ≠ 1 := by
  rw [holonomy_witness]
  intro h
  have h0 : Real.sqrt (4 * (1 - Real.cos (2 * e))) = 0 := by
    rw [← frobNorm_torus_sub_one, h, AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self]
    exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  rw [sqrt_four_one_sub_cos] at h0
  have hs : 0 < Real.sin (2 * e / 2) := by
    rw [show 2 * e / 2 = e by ring]
    exact Real.sin_pos_of_pos_of_lt_pi he (by linarith)
  rw [abs_of_pos hs] at h0
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h0, hs, h8]

/-- **CONTROL — the constant family cannot reach this rate.** `BlockedBackground.blocking_ratio_two`
gives the EXACT ratio `√(2(1+t))` on `constU (gOf t)`, and it is below `2` for every admissible
`t`. So the non-constancy of the witness is load-bearing, not decoration. -/
theorem constant_family_below_two (t : ℝ) (ht : -1 ≤ t) (ht' : t < 1) :
    Real.sqrt (2 * (1 + t)) < 19 / 4 := by
  have h : Real.sqrt (2 * (1 + t)) < Real.sqrt 4 := by
    apply Real.sqrt_lt_sqrt (by linarith)
    linarith
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith

/-! ### §7a — GARBAGE SUBSTITUTION (S82) AND AN INDEPENDENT CROSS-CHECK OF §4

The transfer machinery of §4 must not be able to return `19/4` no matter what it is fed. Feed it a
CONSTANT angle field: every loop then closes on itself (`A₁` and `A₃` run along the same path
length, `A₂` cancels the coarse bond) and the blocked angle collapses to `ell·e` — the pure
telescoping rate, `2` at `ell = 2`. This is proved for arbitrary `s`, `ell`, `c` and `L`, with NO
enumeration, so it is not the same computation with different numbers.

It is also an INDEPENDENT CROSS-CHECK. `BlockedBackground.ubarSU2_constU` proves, by a route that
never touches `pathAngle`, that blocking a CONSTANT configuration is the `ell`-th power map. On a
constant torus configuration the two routes must agree, and `transfer_cross_check` asserts both
values and their equality. If §4's bookkeeping had a dropped leg, a wrong inverse, or a wrong
weight, the two would part company here. -/

theorem pathAngle_const (s : ℕ) (e : ℝ) (y : PeriodicLatticeSite L) (P : List (Fin 3)) :
    pathAngle s (fun _ => e) y P = (P.length : ℝ) * e := by
  induction P generalizing y with
  | nil => simp
  | cons μ rest ih =>
      rw [pathAngle_cons, ih, List.length_cons]
      push_cast
      ring

/-- Every block loop angle of a CONSTANT angle field is `0`, at every stride, block size, bond and
extent. -/
theorem loopAngle_const (s ell : ℕ) (e : ℝ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) : loopAngle s ell (fun _ => e) c x = 0 := by
  unfold loopAngle bondAngle
  rw [pathAngle_const, pathAngle_const, pathAngle_const, pathAngle_const]
  ring

/-- **THE COLLAPSE.** A constant angle field blocks to `ell·e` — not `19/4·e`. -/
theorem blkAngle_const (s ell : ℕ) (e : ℝ) (c : PeriodicLatticeEdge L) :
    blkAngle s ell (fun _ => e) c = (ell : ℝ) * e := by
  unfold blkAngle bondAngle
  simp [loopAngle_const, pathAngle_const]

theorem torusCfg_const (e : ℝ) :
    torusCfg (fun _ : PeriodicLatticeEdge L => e)
      = AdalyFormal.Balaban.CovariantFibreTransfer.constU (torus e) L := rfl

/-- **THE CROSS-CHECK.** §4's transfer and the tree's independently proved `ubarSU2_constU` agree
on the constant torus configuration, and the common value is `torus (2e) = (torus e)²`. No
hypothesis on `e` is needed: the loop angles are identically `0`, hence trivially inside the
principal branch. -/
theorem transfer_cross_check (e : ℝ) :
    ubarSU2 1 2 (torusCfg (fun _ : PeriodicLatticeEdge LW => e)) cW = torus (2 * e)
      ∧ ubarSU2 1 2 (torusCfg (fun _ : PeriodicLatticeEdge LW => e)) cW = torus e ^ 2 := by
  constructor
  · rw [ubarSU2_torusCfg 1 2 _ cW (fun x _ => by
      rw [loopAngle_const]; exact ⟨le_refl 0, Real.pi_pos⟩), blkAngle_const]
    norm_num
  · rw [torusCfg_const, AdalyFormal.Balaban.BlockedBackground.ubarSU2_constU]
    rfl

/-- The two cross-checked values are the same number, stated so the agreement is asserted and not
merely displayed. -/
theorem transfer_cross_check_agrees (e : ℝ) : torus (2 * e) = torus e ^ 2 :=
  ((transfer_cross_check e).1).symm.trans (transfer_cross_check e).2

/-! ## §9 — THE COMPANION CONTRACT `[R2-PLAQUETTE-GROWTH]`: ITS UNITS, AND THE WITNESS' OWN LEVEL

**A UNIT FINDING, ~~REPORTED NOT FIXED~~ — S75 2026-08-02, `compute/v2_install/`: NOW FIXED, in
the successor register installed in the same pass as this module.** The finding below stands
verbatim and every sentence of it is still true of `Balaban/GoalRegister.lean`, which is untouched.
What changed is that it is no longer only *reported*:
`Balaban/GoalRegisterV2.lean` §2 carries the correction — its `V2b_PlaquetteRateAtPrintedBudget`
pins the contract's constant at `16` instead of the installed contract's free `∃ cP`, and
`GoalRegisterV2.printed_budget_units_bridge` proves the linear→squared conversion
`4(1 − cos 4t) ≤ 16 · 4(1 − cos t)` EXACTLY at every angle (not a small-angle linearization), with
`printed_budget_units_bridge_needs_the_square` as its must-fire at the witness `t = π/4`.
The LAW-4 note is retained because it records why THIS lane could not fix it.

`R2` is stated on `frobSupBond`, a NORM (`frobNorm`). Its companion `R2_PlaquetteGrowthContract` is
stated on `RegularityHolonomy.IsRegularHolonomy`, whose level is `holonomyDefectSq = 4 − 2 Re tr`,
which `holonomyDefectSq_torus` below shows is the SQUARED defect `‖U(∂p) − 1‖²_F`. **So the two
register items live in different powers of the field**, and their constants are not comparable as
written: a per-step NORM factor `k` is a factor `k²` in the contract's units, so `R2`'s threshold
`4` corresponds to `16` there. Nothing in `GoalRegister` §2.1/§2.2 records this, and the two items
sit a dozen lines apart.

What is landed here is the fine side of the contract for the `R2` witness: its units, its exact
defect at the plaquette that carries curvature, and an explicit regularity level `M`. The coarse
side — the blocked configuration's own plaquette level — is NOT landed; see PROGRESS.md for the
measured value and the exact remaining step. -/

/-- The plaquette angle of an angle field: the discrete curl. -/
def plaqAngle (f : PeriodicLatticeEdge L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  f (p.1, p.2.1.1) + f (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
    - f (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - f (p.1, p.2.1.2)

/-- **Transfer, plaquettes.** The holonomy of a torus configuration around a plaquette is `torus`
of its discrete curl — exactly. -/
theorem holonomyElem_torusCfg (f : PeriodicLatticeEdge L → ℝ) (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (torusCfg f) p = torus (plaqAngle f p) := by
  show torus _ * torus _ * (torus _)⁻¹ * (torus _)⁻¹ = _
  rw [torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  congr 1

/-- **THE CONTRACT'S UNITS, PINNED.** `holonomyDefectSq` is `4(1 − cos θ) = ‖torus θ − 1‖²_F` — a
SQUARE. Compare `frobNorm_torus_sub_one`, which is its square root. -/
theorem holonomyDefectSq_torus
    (U : PeriodicLinkConfiguration SU2 L) (p : PeriodicLatticePlaquette L) (θ : ℝ)
    (h : AdalyFormal.Balaban.DeltaPrime.holonomyElem U p = torus θ) :
    AdalyFormal.Balaban.RegularityHolonomy.holonomyDefectSq U p = 4 * (1 - Real.cos θ) := by
  unfold AdalyFormal.Balaban.RegularityHolonomy.holonomyDefectSq
  rw [h, coe_torus, torusM, AdalyFormal.Balaban.SuTwoLogExp.dg_trace,
    show (Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-((θ : ℂ) * Complex.I))).re
      = 2 * Real.cos θ by
      rw [Complex.add_re, AdalyFormal.Balaban.SuTwoLogExp.cexp_re,
        AdalyFormal.Balaban.SuTwoLogExp.cexp_neg_re]; ring]
  ring

/-- The defect and the Frobenius norm of §6 are the same quantity, squared — asserted so the two
units have a compiled bridge and not only a docstring. -/
theorem defectSq_eq_frobNorm_sq (θ : ℝ) :
    4 * (1 - Real.cos θ) = frobNorm ((torus θ : M2) - 1) ^ 2 := by
  rw [frobNorm_torus_sub_one, Real.sq_sqrt]
  nlinarith [Real.cos_le_one θ]

/-- Every bond angle of the witness has modulus exactly `ε`. -/
theorem abs_fW (e : ℝ) (he : 0 ≤ e) (b : PeriodicLatticeEdge LW) : |fW e b| = e := by
  cases hb : negBond b <;> simp [fW, hb, abs_of_nonneg he]

/-- Hence every plaquette angle has modulus at most `4ε` — four bonds, no cancellation assumed. -/
theorem abs_plaqAngle_fW (e : ℝ) (he : 0 ≤ e) (p : PeriodicLatticePlaquette LW) :
    |plaqAngle (fW e) p| ≤ 4 * e := by
  unfold plaqAngle
  have h1 := abs_fW e he (p.1, p.2.1.1)
  have h2 := abs_fW e he (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
  have h3 := abs_fW e he (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
  have h4 := abs_fW e he (p.1, p.2.1.2)
  have b1 := abs_le.mp (le_of_eq h1)
  have b2 := abs_le.mp (le_of_eq h2)
  have b3 := abs_le.mp (le_of_eq h3)
  have b4 := abs_le.mp (le_of_eq h4)
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

/-- **THE WITNESS' FINE REGULARITY LEVEL, EXPLICITLY.** `M = 4(1 − cos 4ε)` in the contract's own
squared units. This is the `M` a discharge of `[R2-PLAQUETTE-GROWTH]` would have to carry through
the blocking step for this configuration. -/
theorem witness_IsRegularHolonomy {e : ℝ} (he : 0 ≤ e) (h4 : 4 * e ≤ Real.pi) :
    AdalyFormal.Balaban.RegularityHolonomy.IsRegularHolonomy (VW e)
      (4 * (1 - Real.cos (4 * e))) := by
  intro p
  have hp : AdalyFormal.Balaban.DeltaPrime.holonomyElem (VW e) p = torus (plaqAngle (fW e) p) :=
    holonomyElem_torusCfg (fW e) p
  rw [holonomyDefectSq_torus _ p _ hp]
  have habs := abs_plaqAngle_fW e he p
  have hcos : Real.cos (4 * e) ≤ Real.cos (plaqAngle (fW e) p) := by
    rw [← Real.cos_abs (plaqAngle (fW e) p)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) h4 habs
  linarith

/-- **THE WITNESS' DEFECT AT THE PLAQUETTE THAT CARRIES CURVATURE, EXACTLY.** `4(1 − cos 2ε)`, so
the level is attained at `2ε`, not merely bounded by `4ε`. -/
theorem witness_fine_defect (e : ℝ) :
    AdalyFormal.Balaban.RegularityHolonomy.holonomyDefectSq (VW e)
      (st 0 0 1, ⟨(1, 2), by decide⟩) = 4 * (1 - Real.cos (2 * e)) :=
  holonomyDefectSq_torus _ _ _ (holonomy_witness e)

/-! ## §8 — AXIOM AUDIT -/

#print axioms torus_eq_diagSU2
#print axioms frobNorm_torus_sub_one
#print axioms torus_inv
#print axioms torusCfg
#print axioms pathAngle
#print axioms coarsePathHolonomy_torusCfg
#print axioms bondAngle
#print axioms loopAngle
#print axioms coarseBondVar_torusCfg
#print axioms loopVar_torusCfg
#print axioms blkAngle
#print axioms ubarSU2_torusCfg
#print axioms st
#print axioms shift_st_0
#print axioms shift_st_1
#print axioms shift_st_2
#print axioms cW
#print axioms negBond
#print axioms fW
#print axioms VW
#print axioms fW_pos
#print axioms fW_neg
#print axioms block_eq
#print axioms cPlus_eq
#print axioms replicate_two
#print axioms gamma_000
#print axioms gamma_001
#print axioms gamma_010
#print axioms gamma_011
#print axioms gamma_100
#print axioms gamma_101
#print axioms gamma_110
#print axioms gamma_111
#print axioms loop_000
#print axioms loop_001
#print axioms loop_010
#print axioms loop_011
#print axioms loop_100
#print axioms loop_101
#print axioms loop_110
#print axioms loop_111
#print axioms bondAngle_cW
#print axioms blkAngle_cW
#print axioms loop_branch
#print axioms ubarSU2_VW
#print axioms four_one_sub_cos
#print axioms sqrt_four_one_sub_cos
#print axioms frobNorm_VW
#print axioms frobSupBond_VW
#print axioms cCoarse
#print axioms ubarCoarse_VW_at
#print axioms frobSupBond_ubarCoarse_VW_ge
#print axioms strict_comparison
#print axioms blocking_rate_ge_19_4
#print axioms no_uniform_constant_below_19_4
#print axioms blocking_rate_sandwich
#print axioms prescaling_budget_deficit
#print axioms prescaling_does_not_absorb
#print axioms frobSupBond_VW_pos
#print axioms holonomy_witness
#print axioms witness_has_curvature
#print axioms constant_family_below_two
#print axioms pathAngle_const
#print axioms loopAngle_const
#print axioms blkAngle_const
#print axioms torusCfg_const
#print axioms transfer_cross_check
#print axioms transfer_cross_check_agrees
#print axioms plaqAngle
#print axioms holonomyElem_torusCfg
#print axioms holonomyDefectSq_torus
#print axioms defectSq_eq_frobNorm_sq
#print axioms abs_fW
#print axioms abs_plaqAngle_fW
#print axioms witness_IsRegularHolonomy
#print axioms witness_fine_defect

end AdalyFormal.Balaban.AbelianBlockingRate
