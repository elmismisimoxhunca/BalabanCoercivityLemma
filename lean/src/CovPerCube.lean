/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovWitness

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# `CovPerCube` — PER-CUBE GAUGES GLUE, AND THE PRICE IS THE PER-CUBE RADIUS PLUS THE MISMATCH

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## What this replaces

`drift_percube`'s `DriftTriangle.frobSupBond_le_of_percube` proves

    α₁(U)  ≤  r + ρ ,        ρ := sup over ALL bonds of ‖(1^{γ_i⁻¹})_b − 1‖

— `r` the per-cube gauged radius and `ρ` the ROUGHNESS of each cube's gauge, a quantity that is
**nonzero even when all the cubes carry the SAME nontrivial gauge** (a single constant gauge `g`
has `(1^{g⁻¹})_b = 1`, but a single *varying* gauge does not).  That is the binder
`drift_percube` §1(c) had to add and could not remove, and §1(d) proves it cannot be removed while
the reference stays FLAT.

Here the reference moves with the gauge (`CovTerminal` §3), so what has to be paid is not the
roughness of each gauge but only the **MISMATCH between the gauges of two cubes at a shared site**:

    α₁(U^{γ*})  ≤  r + m ,   γ*(x) := γ_{cube(x)}(x),
    m := sup over bonds of ‖γ_{cube(b₋)}(b₊) · γ_{cube(b₊)}(b₊)⁻¹ − 1‖

and `m = 0` on every bond whose two endpoints lie in the SAME cube (§2b, a theorem, not a remark),
hence `m = 0` outright when the per-cube gauges agree — in particular when they are all EQUAL,
where `ρ` is still whatever the common gauge's roughness happens to be (§2d measures that gap at an
explicit configuration).

## The assignment is TOTAL, on purpose (S83)

The cube structure enters as a total function `assign : sites → ι`, so the partition is complete
and disjoint BY TYPING: there is no covering hypothesis that could quietly omit a class of bonds
and no disjointness hypothesis that could be satisfied vacuously.  Every bond of the torus is
priced, and the crossing bonds are exactly those with `assign b₋ ≠ assign b₊`.
-/

namespace AdalyFormal.CovariantDatum

open AdalyFormal.Balaban
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeInv)
open AdalyFormal.Balaban.RegularUQChain (frobNorm_add_le su_coe_inv)
open AdalyFormal.HrawCarriers (ScaleQuotient)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — RIGHT MULTIPLICATION BY A SPECIAL UNITARY IS A FROBENIUS ISOMETRY

`RMapLipschitz.frobSq_mul_right_isometry` is the brick (CITED); only the `SU(2)` packaging is new,
and it is the mirror of `RegularUQChain.frobNorm_mul_left_iso`, which `DriftTriangle` already
uses on the other side. -/

theorem frobNorm_mul_su_right (M : Matrix (Fin 2) (Fin 2) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    RMapLipschitz.frobNorm (M * (g : Matrix (Fin 2) (Fin 2) ℂ)) = RMapLipschitz.frobNorm M := by
  have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp g.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  show Real.sqrt (RMapLipschitz.frobSq _) = Real.sqrt (RMapLipschitz.frobSq _)
  rw [RMapLipschitz.frobSq_mul_right_isometry M (g : Matrix (Fin 2) (Fin 2) ℂ) hg]

/-- **THE PRODUCT SPLIT**: `‖XY − 1‖ ≤ ‖X − 1‖ + ‖Y − 1‖` for `X, Y ∈ SU(2)`.  This is the whole
analytic content of §2. -/
theorem frobNorm_mul_sub_one_le (X Y : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    RMapLipschitz.frobNorm (((X * Y : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ RMapLipschitz.frobNorm ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        + RMapLipschitz.frobNorm ((Y : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hcoe : ((X * Y : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  have hsplit : (X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) * (Y : Matrix (Fin 2) (Fin 2) ℂ)
        + ((Y : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by noncomm_ring
  rw [hcoe, hsplit]
  refine le_trans (frobNorm_add_le _ _) (le_of_eq ?_)
  rw [frobNorm_mul_su_right]

/-! ## §2 — THE GLUED GAUGE AND ITS PRICE -/

/-- **The glued gauge** `γ*(x) := γ_{assign x}(x)`.  A single global gauge, discontinuous across
cube boundaries — which is legitimate here precisely because `GaugeFn L` carries no regularity and
`CovGauge`'s equivariance covers every gauge (measured, `CovGauge` §1d). -/
def gluedGauge {ι : Type*} (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L) : GaugeFn L :=
  fun x => γ (assign x) x

/-- **§2a — THE BOND-LEVEL SPLIT.**  On EVERY bond, the glued gauge's deviation is the base cube's
own gauged deviation plus the mismatch at the bond's forward endpoint. -/
theorem frobNorm_glued_le {ι : Type*} (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    RMapLipschitz.frobNorm
        (((periodicGaugeTransform (gluedGauge assign γ) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ RMapLipschitz.frobNorm
          (((periodicGaugeTransform (γ (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        + RMapLipschitz.frobNorm
          (((γ (assign b.1) (periodicLatticeShift b.1 b.2)
              * (γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
              Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  set y := periodicLatticeShift b.1 b.2 with hy
  set i := assign b.1 with hi
  set j := assign y with hj
  have hfac : ((periodicGaugeTransform (gluedGauge assign γ) U) b :
      Matrix.specialUnitaryGroup (Fin 2) ℂ)
      = ((periodicGaugeTransform (γ i) U) b) * (γ i y * (γ j y)⁻¹) := by
    show gluedGauge assign γ b.1 * U b * (gluedGauge assign γ y)⁻¹
      = (γ i b.1 * U b * (γ i y)⁻¹) * (γ i y * (γ j y)⁻¹)
    show γ (assign b.1) b.1 * U b * (γ (assign y) y)⁻¹ = _
    rw [← hi, ← hj]
    group
  rw [hfac]
  exact frobNorm_mul_sub_one_le _ _

/-- **§2b — THE MISMATCH VANISHES ON EVERY INTERIOR BOND.**  If both endpoints lie in the same
cube, the mismatch factor is exactly `1` and its deviation is exactly `0`.  So only bonds CROSSING
a cube boundary are charged — this is the precise sense in which "the per-cube price is the whole
price" up to the boundary. -/
theorem mismatch_zero_of_interior {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (γ : ι → GaugeFn L) (b : Bond L)
    (hsame : assign (periodicLatticeShift b.1 b.2) = assign b.1) :
    RMapLipschitz.frobNorm
        (((γ (assign b.1) (periodicLatticeShift b.1 b.2)
            * (γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
            Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
  rw [hsame, mul_inv_cancel]
  show RMapLipschitz.frobNorm ((1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0
  rw [sub_self]
  show Real.sqrt (RMapLipschitz.frobSq 0) = 0
  have : RMapLipschitz.frobSq (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold RMapLipschitz.frobSq
    simp
  rw [this, Real.sqrt_zero]

/-- **§2c — THE GLOBAL BOUND AT THE GLUED GAUGE.**  `α₁(U^{γ*}) ≤ r + m`. -/
theorem frobSupBond_glued_le {ι : Type*} (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r m : ℝ)
    (hclass : ∀ b : Bond L, RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γ (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hmatch : ∀ b : Bond L, RMapLipschitz.frobNorm
      (((γ (assign b.1) (periodicLatticeShift b.1 b.2)
          * (γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ m) :
    frobSupBond (periodicGaugeTransform (gluedGauge assign γ) U) ≤ r + m := by
  unfold frobSupBond
  refine Finset.sup'_le _ _ (fun b _ => ?_)
  exact (frobNorm_glued_le assign γ U b).trans (add_le_add (hclass b) (hmatch b))

/-- **§2d — WHERE THE GAIN IS, EXACTLY.**  With ONE cube (`ι = Unit`) — i.e. a single global gauge
`γ₀`, the case `drift_percube` §1(d)'s pure-gauge witness lives in — the mismatch is identically
`0`, so `m = 0` is admissible and the price is `r` alone.  `DriftTriangle.frobSupBond_le_of_percube`
must still pay `ρ = sup_b ‖(1^{γ₀⁻¹})_b − 1‖`, which for the witness gauge is `≥ 2`. -/
theorem single_cube_mismatch_zero (γ₀ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r : ℝ)
    (hclass : ∀ b : Bond L, RMapLipschitz.frobNorm
      (((periodicGaugeTransform γ₀ U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r) :
    frobSupBond (periodicGaugeTransform
        (gluedGauge (fun _ => ()) (fun _ : Unit => γ₀)) U) ≤ r + 0 := by
  refine frobSupBond_glued_le (fun _ => ()) (fun _ : Unit => γ₀) U r 0 hclass (fun b => ?_)
  exact le_of_eq (mismatch_zero_of_interior (fun _ => ()) (fun _ : Unit => γ₀) b rfl)

/-- The glued gauge of a one-cube family IS that cube's gauge. -/
theorem gluedGauge_single (γ₀ : GaugeFn L) :
    gluedGauge (fun _ => ()) (fun _ : Unit => γ₀) = γ₀ := rfl

/-! ## §3 — FEEDING `CovTerminal` §4b

The per-cube data on the COARSE torus supplies `hsmallUGauged` directly, because
`CovTerminal.coarseGauge_surjective` says every coarse gauge — in particular the glued one — is
induced by a fine gauge. -/

/-- **THE PER-CUBE HYPOTHESIS SUPPLIES THE GAUGED COARSE BINDER.**  Given a cube assignment on the
coarse torus, per-cube gauges, the per-cube radius `r` and the boundary mismatch `m` with
`r + m ≤ 1/(13336·ℓ₀³)`, there IS a fine gauge `γ` whose induced coarse gauge makes
`CovTerminal.terminal_covariant_bothGauged`'s `hsmallUGauged` true.  No roughness binder appears. -/
theorem hsmallUGauged_of_perCube {L' : PeriodicLatticeExtent} {ell ell₀ : ℕ} {ι : Type*}
    (h : ScaleQuotient L ell L')
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (assign : PeriodicLatticeSite L' → ι) (γc : ι → GaugeFn L') (r m : ℝ)
    (hclass : ∀ b : Bond L', RMapLipschitz.frobNorm
      (((periodicGaugeTransform (γc (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r)
    (hmatch : ∀ b : Bond L', RMapLipschitz.frobNorm
      (((γc (assign b.1) (periodicLatticeShift b.1 b.2)
          * (γc (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ m)
    (hsum : r + m ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3)) :
    ∃ γ : GaugeFn L, frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3) := by
  refine ⟨liftCoarseGauge h (gluedGauge assign γc), ?_⟩
  rw [coarseGauge_liftCoarseGauge h (gluedGauge assign γc)]
  exact le_trans (frobSupBond_glued_le assign γc U r m hclass hmatch) hsum

end AdalyFormal.CovariantDatum
