/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import FloorMembership
import CurvedContent
import DriftCentre

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.longLine false

/-!
# `FineDrift` — THE FINE-SIDE GAUGED DRIFT FROM PER-CUBE DATA, AND THE PRICE OF THE BOUNDARY

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## THE SHAPE, ADJUDICATED BEFORE THE BUILD

`FloorMembership.terminal_covariant_printed_perCubeDrift` carries one surviving analytic binder,

    hsmallFineGauged : ‖H₁‖ · rawErrorCoeff ℓ (U_fine^γ)  ≤  1/(4708·ℓ₀³) .

`MechEdges.G16.rawErrorCoeff` is, by definition,

    rawErrorCoeff ℓ V  =  (36√2/√ℓ) · frobSupBond V ,

so the binder is a **`frobSupBond` bound on the gauged fine configuration** — a SUP over bonds
times a scalar.  It is NOT a summation (there is nothing to route through `recompose_sum`), and it
is NOT flat-referenced in any conclusion (`DriftNoGo` does not bind: the reference moves with the
caller's `γ`, exactly as `CovTerminal` §0a records for the coarse half).  Its single consumption
site is the `hhalf` step of `FloorMembership.terminal_covariant_printed`, where it is the second
summand of the real scalar `CovTerminal.gaugedKappa`.

The tool for that shape already exists and is polymorphic in the torus:
`CovPerCube.frobSupBond_glued_le`.  §2 applies it on the FINE torus.

## THE CONSEQUENCE THAT SHAPES THE BUILD

ONE gauge `γ : GaugeFn L` serves BOTH binders (the coarse one at `coarseGauge h γ`).  So feeding
the fine side from per-cube data is not independent of the coarse side — it DETERMINES the coarse
gauge.  §4 proves the determination is exactly a glued gauge again:

    coarseGauge h (gluedGauge assign γf)
      = gluedGauge (assign ∘ emb) (fun i => coarseGauge h (γf i))          — by `rfl`

so a SINGLE per-cube gauge family on the fine torus feeds both binders, with the coarse family
INDUCED rather than chosen.  That is the opaque binder `hγ` of
`FloorMembership.terminal_covariant_printed_perCubeDrift`, discharged.  §5 is the terminal theorem
whose only background-smallness hypotheses are per-cube, on BOTH scales.

## THE BOUNDARY PRICE, PRICED RATHER THAN ASSUMED AWAY

`frobSupBond_glued_le` charges `r + m`, `m` the sup of the mismatch over bonds.  §6 settles what
`m` costs, in three theorems and no adjectives:

* §6a `m = 0` whenever the per-cube gauges AGREE at the crossed sites (interior bonds are the
  special case already in `CovPerCube` §2b);
* §6b/§6c that agreement **collapses the family to a single global gauge, bond by bond** — under
  matching, per-cube data at radius `r` is EQUIVALENT to `frobSupBond (U^{γ*}) ≤ r`.  So all of the
  per-cube quantifier's extra strength lives in `m > 0`;
* §6d **the price does not amortise over the cover.**  For ANY cube assignment with at least one
  crossing bond — of any cube side whatsoever — there are per-cube gauges with per-cube radius
  EXACTLY `0` whose glued configuration has `frobSupBond ≥ 2`.  Surface-to-volume is the ratio that
  prices a SUM; the consumed object is a SUP, which carries no volume normalisation, and the ratio
  never appears.  §6e runs that at three distinct cube thicknesses on the `4³` torus.

## §3'S CONSTANT IS EXACT, NOT FITTED

`fineRadius ℓ ℓ₀ K = √(2ℓ)/(338976·K·ℓ₀³)` and `K·(36√2/√ℓ)·fineRadius = 1/(4708·ℓ₀³)` is an
EQUALITY (`fineRadius_prices_exactly`).  `338976 = 72·4708 = 2·36·4708`: `36√2` is
`rawErrorCoeff`'s own counted constant and `4708` is `FloorMembership` §1's fine half-budget.
Nothing is fitted and nothing is slack — §8 shows doubling the radius doubles the price exactly.

## ISLAND

Nothing is installed in `formal/`; nothing enters `Spine.lean`'s import cone; nothing contributes
to `FULL3D.main`'s axiom set.
-/

namespace AdalyFormal.FineDrift

open AdalyFormal.Balaban
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 witnessMElem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.LocalizedEstimates (CSite)
open AdalyFormal.Balaban.RecomposeSum (CubesRefine)
open AdalyFormal.Balaban.DriftPerCube (frobNorm_constGauge frobNorm_witnessM_sub_one)
open AdalyFormal.Balaban.SuTwoLogExp (torus)
open AdalyFormal.Balaban.AbelianBlockingRate (torus_inv frobNorm_torus_sub_one
  sqrt_four_one_sub_cos)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale coarseSiteEquiv feedPen)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawErrorCoeff rawErrorCoeff_nonneg)
open AdalyFormal.TerminalBinder (feedDatumGen)
open AdalyFormal.CovariantDatum (coarseGauge gluedGauge frobSupBond_glued_le
  mismatch_zero_of_interior)
open AdalyFormal.FloorMembership (terminal_covariant_printed_perCubeDrift)

variable {L L' : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §0 — NOTATION FOR THE TWO REPEATED PREDICATES

Both are copied binder-for-binder from `CovPerCube.frobSupBond_glued_le`; naming them keeps every
statement below readable without changing a single quantifier. -/

/-- **THE PER-CUBE CLASS**: on every bond, the deviation measured at the gauge of the cube owning
the bond's BACKWARD endpoint is at most `r`.  (`CovPerCube`'s `hclass`, verbatim.) -/
def PerCubeClass {ι : Type*} (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r : ℝ) : Prop :=
  ∀ b : Bond L, RMapLipschitz.frobNorm
    (((periodicGaugeTransform (γ (assign b.1)) U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ r

/-- **THE BOUNDARY MISMATCH**: on every bond, the two cubes' gauges at the FORWARD endpoint differ
by at most `m`.  (`CovPerCube`'s `hmatch`, verbatim.) -/
def MismatchBound {ι : Type*} (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (m : ℝ) : Prop :=
  ∀ b : Bond L, RMapLipschitz.frobNorm
    (((γ (assign b.1) (periodicLatticeShift b.1 b.2)
        * (γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ m

/-! ## §1 — THE OBJECT UNDER THE BINDER IS `frobSupBond` TIMES A SCALAR -/

/-- **THE SHAPE ADJUDICATION, IN THE KERNEL.**  `rawErrorCoeff` is definitionally a scalar multiple
of `frobSupBond`.  Everything in this file is a consequence of this one line. -/
theorem rawErrorCoeff_eq (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    rawErrorCoeff ell U = (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond U := rfl

theorem fineCoeff_nonneg (ell : ℕ) : (0 : ℝ) ≤ 36 * Real.sqrt 2 / Real.sqrt (ell : ℝ) := by
  positivity

/-! ## §2 — THE GLUED BOUND, ON THE FINE TORUS -/

/-- **§2 — PER-CUBE DATA BOUNDS THE FINE ERROR COEFFICIENT AT THE GLUED GAUGE.**
`CovPerCube.frobSupBond_glued_le` is polymorphic in the torus; this is that theorem read through
§1's identity, on `L` rather than `L'`. -/
theorem rawErrorCoeff_glued_le {ι : Type*} (ell : ℕ)
    (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r m : ℝ)
    (hclass : PerCubeClass assign γ Ufine r) (hmatch : MismatchBound assign γ m) :
    rawErrorCoeff ell (periodicGaugeTransform (gluedGauge assign γ) Ufine)
      ≤ (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * (r + m) := by
  rw [rawErrorCoeff_eq]
  exact mul_le_mul_of_nonneg_left
    (frobSupBond_glued_le assign γ Ufine r m hclass hmatch) (fineCoeff_nonneg ell)

/-! ## §3 — THE PRICE, AND IT IS EXACT -/

/-- **THE FINE PER-CUBE RADIUS.**  `√(2ℓ)/(338976·K·ℓ₀³)`, with `K = ‖H₁‖`.  Every factor is
counted: `338976 = 2·36·4708`, `36√2` being `rawErrorCoeff`'s own constant and `4708` being
`FloorMembership` §1's fine half of the drift budget. -/
noncomputable def fineRadius (ell ell₀ : ℕ) (K : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt (ell : ℝ) / (338976 * K * (ell₀ : ℝ) ^ 3)

/-- The same radius written with a single square root, `√(2ℓ)`. -/
theorem fineRadius_eq_sqrt_two_ell (ell ell₀ : ℕ) (K : ℝ) :
    fineRadius ell ell₀ K = Real.sqrt (2 * (ell : ℝ)) / (338976 * K * (ell₀ : ℝ) ^ 3) := by
  unfold fineRadius
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem fineRadius_pos {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀) {K : ℝ} (hK : 0 < K) :
    0 < fineRadius ell ell₀ K := by
  have h1 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h2 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hse : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr h1
  have hden : (0 : ℝ) < 338976 * K * (ell₀ : ℝ) ^ 3 := by positivity
  exact div_pos (mul_pos hs2 hse) hden

/-- **THE CONSTANT IS EXACT.**  At the radius, the priced quantity is EQUAL to the budget — there
is no slack anywhere in `fineRadius`, and the factorisation `338976 = 72·4708` is what makes it so.
An equality, so a mutation of any factor in `fineRadius` changes the value and must fire. -/
theorem fineRadius_prices_exactly {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    {K : ℝ} (hK : 0 < K) :
    K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K)
      = 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h2 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
  have hse : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr h1
  have hsne : Real.sqrt (ell : ℝ) ≠ 0 := ne_of_gt hse
  have hKne : K ≠ 0 := ne_of_gt hK
  have h2ne : ((ell₀ : ℝ)) ≠ 0 := ne_of_gt h2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hexp : K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K)
      = (Real.sqrt 2 * Real.sqrt 2) * (36 * K * Real.sqrt (ell : ℝ))
        / (Real.sqrt (ell : ℝ) * (338976 * K * (ell₀ : ℝ) ^ 3)) := by
    unfold fineRadius
    field_simp
  rw [hexp, hs2]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **§3 HEADLINE — THE FINE BINDER, FROM PER-CUBE DATA.**  `FloorMembership`'s last analytic
binder `hsmallFineGauged`, discharged at the glued gauge from per-cube deviations and the boundary
mismatch alone.  `frobSupBond U_fine` — the flat reference — does not appear. -/
theorem hsmallFineGauged_of_perCube {ι : Type*} {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    (K : ℝ) (hK : 0 < K)
    (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r m : ℝ)
    (hclass : PerCubeClass assign γ Ufine r) (hmatch : MismatchBound assign γ m)
    (hsum : r + m ≤ fineRadius ell ell₀ K) :
    K * rawErrorCoeff ell (periodicGaugeTransform (gluedGauge assign γ) Ufine)
      ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  have hg := rawErrorCoeff_glued_le ell assign γ Ufine r m hclass hmatch
  have hstep : (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * (r + m)
      ≤ (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K :=
    mul_le_mul_of_nonneg_left hsum (fineCoeff_nonneg ell)
  calc K * rawErrorCoeff ell (periodicGaugeTransform (gluedGauge assign γ) Ufine)
      ≤ K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K) :=
        mul_le_mul_of_nonneg_left (le_trans hg hstep) (le_of_lt hK)
    _ = 1 / (4708 * (ell₀ : ℝ) ^ 3) := fineRadius_prices_exactly hell hell₀ hK

/-! ## §4 — THE COUPLING: ONE FINE CUBE FAMILY INDUCES THE COARSE ONE

The chain's `γ` is a SINGLE fine gauge serving both binders.  Taking it to be a glued gauge on the
fine torus determines the coarse gauge — and §4b shows the determined object is again a glued gauge,
for the INDUCED cube family.  This is what turns `FloorMembership` §3c's opaque coupling binder
`hγ : coarseGauge h γ = gluedGauge assign γc` into a `rfl`. -/

/-- The cube assignment induced on the COARSE torus: a coarse site is assigned the cube of the fine
site it embeds to. -/
def inducedCoarseAssign {ι : Type*} (h : ScaleQuotient L ell L')
    (assign : PeriodicLatticeSite L → ι) : PeriodicLatticeSite L' → ι :=
  fun z => assign (((coarseSiteEquiv h).symm z).1)

/-- The per-cube gauges induced on the COARSE torus: each cube's fine gauge, restricted. -/
def inducedCoarseGauges {ι : Type*} (h : ScaleQuotient L ell L')
    (γ : ι → GaugeFn L) : ι → GaugeFn L' :=
  fun i => coarseGauge h (γ i)

/-- **§4b — THE COUPLING LEMMA.**  The coarse gauge of a fine glued gauge IS the glued gauge of the
induced coarse family.  `rfl`: both sides evaluate at `z` to `γ (assign (emb z)) (emb z)`. -/
theorem coarseGauge_gluedGauge {ι : Type*} (h : ScaleQuotient L ell L')
    (assign : PeriodicLatticeSite L → ι) (γ : ι → GaugeFn L) :
    coarseGauge h (gluedGauge assign γ)
      = gluedGauge (inducedCoarseAssign h assign) (inducedCoarseGauges h γ) := rfl

/-! ## §5 — THE TERMINAL THEOREM: PER-CUBE ON BOTH SCALES -/

/-- **§5 HEADLINE — EVERY BACKGROUND-SMALLNESS HYPOTHESIS IS PER-CUBE, ON BOTH SCALES.**

`FloorMembership.terminal_covariant_printed_perCubeDrift` with `hsmallFineGauged` DISCHARGED and the
coupling binder `hγ` GONE.  The gauge is not a binder any more: it is `gluedGauge assignF γf`,
assembled from the fine cube family, and the coarse per-cube data is stated at the INDUCED family.

    ℓ₀ ≥ 2 on a tiled torus,
    CMP99b (3.35) on a cube family 𝒞src with c·M·α₀ < 1/(1120·ℓ₀³),        [floor, per cube]
    [GEOM] CubesRefine,
    coarse per-cube (rC, mC) at the INDUCED family, rC + mC ≤ 1/(26672·ℓ₀³),  [drift, per cube]
    fine   per-cube (rF, mF) on the fine torus,   rF + mF ≤ fineRadius ℓ ℓ₀ ‖H₁‖, [drift, per cube]
    δ < 1/(5480006400·ℓ₀⁶·σ₀²·‖H₁‖·c₂·‖T‖√(2|Bond L'|))
  ⟹ ⟨B̃, C*Δ_k(U) C B̃⟩ > 0  for every B̃ ≠ 0.

Neither `frobSupBond U` nor `frobSupBond U_fine` appears. -/
theorem terminal_perCube_bothScales {ell₀ : ℕ} {ι : Type*} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (assignF : PeriodicLatticeSite L → ι) (γf : ι → GaugeFn L)
    (rC mC rF mF : ℝ)
    (hclassC : PerCubeClass (inducedCoarseAssign h assignF) (inducedCoarseGauges h γf) U rC)
    (hmatchC : MismatchBound (inducedCoarseAssign h assignF) (inducedCoarseGauges h γf) mC)
    (hsumC : rC + mC ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hclassF : PerCubeClass assignF γf Ufine rF) (hmatchF : MismatchBound assignF γf mF)
    (hsumF : rF + mF ≤ fineRadius ell ell₀
      ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα₀ : 0 ≤ α₀) (hprintedThr : c * M * α₀ < 1 / (1120 * (ell₀ : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond L'))) (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine hdvd0 (Finset.univ : Finset (CSite L' ell₀))
      (fun z => ({z} : Finset (CSite L' ell₀))) 𝒞src)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (5480006400 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hell0 : 0 < ell₀ := by omega
  have hellpos : 0 < ell := ell_pos_of_scale h
  have hfine : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform (gluedGauge assignF γf) Ufine)
      ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) :=
    hsmallFineGauged_of_perCube hellpos hell0 _ hH1 assignF γf Ufine rF mF hclassF hmatchF hsumF
  exact terminal_covariant_printed_perCubeDrift h Ufine (gluedGauge assignF γf) hell2 hstrict hdvd0
    U (inducedCoarseAssign h assignF) (inducedCoarseGauges h γf) rC mC
    (coarseGauge_gluedGauge h assignF γf) hclassC hmatchC hsumC bc heps hfine
    c M α₀ η Lj hη hηne hLj hc hM hα₀ hprintedThr 𝒞src hprinted hgeom Qext T S hS c₂ hc₂ hD2
    δ hδ0 hU hH1 hT hcard hδ w hw

/-! ### §5b — NOTHING IS LOST: THE ONE-CUBE FAMILY RECOVERS THE GLOBAL-GAUGE FORM

A per-cube hypothesis could be a WEAKENING dressed as a generalisation, so this is the control that
§5 is not one.  The one-cube family (`ι = Unit`) has `gluedGauge (fun _ => ()) (fun _ => γ) = γ` by
`rfl`, its mismatch is `0`, and its per-cube class is EXACTLY `frobSupBond (U^γ) ≤ r`.  §5
instantiated there is `FloorMembership` §3c at an arbitrary caller-chosen gauge with both smallness
conditions global.  So §5 CONTAINS the previous shape and adds the incoherent families on top of it.
-/

/-- The one-cube glued gauge IS the gauge. -/
theorem gluedGauge_single_eq (γ : GaugeFn L) :
    gluedGauge (fun _ => ()) (fun _ : Unit => γ) = γ := rfl

/-- The one-cube family has no boundary: its mismatch is `0`.  `CovPerCube` §2b at `hsame = rfl`. -/
theorem mismatchBound_single (γ : GaugeFn L) :
    MismatchBound (fun _ => ()) (fun _ : Unit => γ) 0 :=
  fun b => le_of_eq (mismatch_zero_of_interior (fun _ => ()) (fun _ : Unit => γ) b rfl)

/-- The one-cube per-cube class IS the global `frobSupBond` bound. -/
theorem perCubeClass_single_iff (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r : ℝ) :
    PerCubeClass (fun _ => ()) (fun _ : Unit => γ) U r
      ↔ frobSupBond (periodicGaugeTransform γ U) ≤ r := by
  constructor
  · intro hcl
    unfold frobSupBond
    exact Finset.sup'_le _ _ (fun b _ => hcl b)
  · intro hsup b
    exact le_trans (frobNorm_le_frobSupBond (periodicGaugeTransform γ U) b) hsup

/-- **§5b — §5 AT ONE CUBE IS THE GLOBAL-GAUGE STATEMENT.**  Both drift conditions are stated at a
single caller-chosen `γ`; no per-cube data is needed to use §5 in the shape the chain already had.
The fine condition is `frobSupBond (U_fine^γ) ≤ fineRadius`, which is §3's radius read as a bound on
the configuration rather than on a family. -/
theorem terminal_perCube_bothScales_at_globalGauge {ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (γ : GaugeFn L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallUGauged : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (26672 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFine : frobSupBond (periodicGaugeTransform γ Ufine)
      ≤ fineRadius ell ell₀
        ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα₀ : 0 ≤ α₀) (hprintedThr : c * M * α₀ < 1 / (1120 * (ell₀ : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond L'))) (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine hdvd0 (Finset.univ : Finset (CSite L' ell₀))
      (fun z => ({z} : Finset (CSite L' ell₀))) 𝒞src)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (5480006400 * (ell₀ : ℝ) ^ 6 * (rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  refine terminal_perCube_bothScales h Ufine hell2 hstrict hdvd0 U (fun _ => ())
    (fun _ : Unit => γ) (1 / (26672 * (ell₀ : ℝ) ^ 3)) 0
    (fineRadius ell ell₀ ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖) 0
    ?_ ?_ ?_ bc heps ?_ ?_ ?_ c M α₀ η Lj hη hηne hLj hc hM hα₀ hprintedThr 𝒞src hprinted hgeom
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw
  · exact (perCubeClass_single_iff (coarseGauge h γ) U
      (1 / (26672 * (ell₀ : ℝ) ^ 3))).mpr hsmallUGauged
  · exact mismatchBound_single (coarseGauge h γ)
  · linarith
  · exact (perCubeClass_single_iff γ Ufine
      (fineRadius ell ell₀
        ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖)).mpr hsmallFine
  · exact mismatchBound_single γ
  · linarith

/-! ## §6 — WHAT THE BOUNDARY COSTS, IN THEOREMS -/

/-- The Frobenius norm of `1 − 1` is `0`; used three times below. -/
theorem frobNorm_one_sub_one :
    RMapLipschitz.frobNorm (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
  show RMapLipschitz.frobNorm ((1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0
  rw [sub_self]
  exact RMapLipschitz.frobNorm_zero

/-- **§6a — THE MISMATCH VANISHES UNDER BOUNDARY MATCHING.**  The hypothesis is imposed only on
CROSSING bonds; interior bonds satisfy it automatically (`CovPerCube` §2b). -/
theorem mismatch_zero_of_boundaryMatch {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (γ : ι → GaugeFn L)
    (hmatch : ∀ b : Bond L, assign (periodicLatticeShift b.1 b.2) ≠ assign b.1 →
      γ (assign b.1) (periodicLatticeShift b.1 b.2)
        = γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2)) :
    MismatchBound assign γ 0 := by
  intro b
  by_cases hs : assign (periodicLatticeShift b.1 b.2) = assign b.1
  · exact le_of_eq (mismatch_zero_of_interior assign γ b hs)
  · rw [hmatch b hs, mul_inv_cancel]
    exact le_of_eq frobNorm_one_sub_one

/-- **§6b — UNDER MATCHING THE GLUED GAUGE AGREES WITH THE OWNING CUBE'S GAUGE, BOND BY BOND.** -/
theorem glued_eq_perCube_of_boundaryMatch {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (γ : ι → GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hmatch : ∀ b : Bond L, assign (periodicLatticeShift b.1 b.2) ≠ assign b.1 →
      γ (assign b.1) (periodicLatticeShift b.1 b.2)
        = γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))
    (b : Bond L) :
    (periodicGaugeTransform (gluedGauge assign γ) U) b
      = (periodicGaugeTransform (γ (assign b.1)) U) b := by
  have hy : γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2)
      = γ (assign b.1) (periodicLatticeShift b.1 b.2) := by
    by_cases hs : assign (periodicLatticeShift b.1 b.2) = assign b.1
    · rw [hs]
    · exact (hmatch b hs).symm
  show gluedGauge assign γ b.1 * U b * (gluedGauge assign γ (periodicLatticeShift b.1 b.2))⁻¹
    = γ (assign b.1) b.1 * U b * (γ (assign b.1) (periodicLatticeShift b.1 b.2))⁻¹
  show γ (assign b.1) b.1 * U b
      * (γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2))⁻¹ = _
  rw [hy]

/-- **§6c — MATCHING COLLAPSES THE PER-CUBE FAMILY TO ONE GLOBAL GAUGE.**  An IFF: with `m = 0`
available, per-cube data at radius `r` says exactly `frobSupBond (U^{γ*}) ≤ r` for the single glued
gauge `γ*`.  **So every bit of strength the per-cube quantifier has over a global gauge lives in
`m > 0`** — which is the price §6d shows cannot be amortised. -/
theorem perCube_iff_global_of_boundaryMatch {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (γ : ι → GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r : ℝ)
    (hmatch : ∀ b : Bond L, assign (periodicLatticeShift b.1 b.2) ≠ assign b.1 →
      γ (assign b.1) (periodicLatticeShift b.1 b.2)
        = γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2)) :
    PerCubeClass assign γ U r
      ↔ frobSupBond (periodicGaugeTransform (gluedGauge assign γ) U) ≤ r := by
  constructor
  · intro hcl
    unfold frobSupBond
    refine Finset.sup'_le _ _ (fun b _ => ?_)
    rw [glued_eq_perCube_of_boundaryMatch assign γ U hmatch b]
    exact hcl b
  · intro hsup b
    have hb := frobNorm_le_frobSupBond (periodicGaugeTransform (gluedGauge assign γ) U) b
    rw [glued_eq_perCube_of_boundaryMatch assign γ U hmatch b] at hb
    exact le_trans hb hsup

/-- **§6d — THE BOUNDARY PRICE DOES NOT AMORTISE OVER THE COVER.**

For ANY cube assignment whatsoever with at least one crossing bond — any cube side, any shape, any
index type — there are per-cube gauges whose per-cube radius is EXACTLY `0` and whose glued
configuration has `frobSupBond ≥ 2`.  The background is the FLAT one, so nothing here is charged to
the configuration: the whole `2` is mismatch.

**Hence the mismatch term of `frobSupBond_glued_le` cannot be dropped, and no geometric parameter
of the cover can make it small.**  Surface-to-volume prices a SUM; `frobSupBond` is a SUP, and a sup
carries no volume normalisation, so the ratio never enters.  The gauges are CONSTANT on each cube —
the cheapest possible per-cube data — which is why the radius is `0` rather than merely small. -/
theorem mismatch_price_not_removable {ι : Type*} [DecidableEq ι]
    (assign : PeriodicLatticeSite L → ι) (b : Bond L)
    (hcross : assign (periodicLatticeShift b.1 b.2) ≠ assign b.1) :
    ∃ γ : ι → GaugeFn L,
      PerCubeClass assign γ (trivialU L) 0
        ∧ 2 ≤ frobSupBond (periodicGaugeTransform (gluedGauge assign γ) (trivialU L)) := by
  classical
  refine ⟨fun i => fun _ => (if i = assign b.1 then witnessMElem else 1), ?_, ?_⟩
  · intro c
    rw [frobNorm_constGauge]
    exact le_of_eq frobNorm_one_sub_one
  · have hb := frobNorm_le_frobSupBond
      (periodicGaugeTransform
        (gluedGauge assign (fun i => fun _ => (if i = assign b.1 then witnessMElem else 1)))
        (trivialU L)) b
    have hval : (periodicGaugeTransform
        (gluedGauge assign (fun i => fun _ => (if i = assign b.1 then witnessMElem else 1)))
        (trivialU L)) b = witnessMElem := by
      show (if assign b.1 = assign b.1 then witnessMElem else 1) * (1 : SU2)
        * (if assign (periodicLatticeShift b.1 b.2) = assign b.1 then witnessMElem else 1)⁻¹
          = witnessMElem
      rw [if_pos rfl, if_neg hcross, inv_one, mul_one, mul_one]
    rw [hval, frobNorm_witnessM_sub_one] at hb
    exact hb

/-! ### §6e — THE SAME AT THREE DISTINCT CUBE THICKNESSES ON THE `4³` TORUS

§6d is stated for an arbitrary assignment, so it applies at every cube side; §6e exhibits actual
covers of the `4³` torus at thicknesses `1`, `2` and `3` and checks by decision procedure that each
has a crossing bond.  The price is `2` at every one of them: the cover's side is a free parameter
of the caller, and the price is INVARIANT under it. -/

/-- A site of the `4³` torus with all coordinates equal to `v`. -/
def wSite (v : Fin 4) : PeriodicLatticeSite witnessL := fun _ => v

/-- The thickness-`c` slab cover of the `4³` torus in direction `0`. -/
def thickSlab (c : ℕ) (x : PeriodicLatticeSite witnessL) : Bool := decide ((x 0 : ℕ) < c)

/-- Thickness `1`: the bond at the origin crosses. -/
theorem thickSlab1_crossing :
    thickSlab 1 (periodicLatticeShift (wSite 0) (0 : Fin 3)) ≠ thickSlab 1 (wSite 0) := by decide

/-- Thickness `2`: the bond based at `x₀ = 1` crosses. -/
theorem thickSlab2_crossing :
    thickSlab 2 (periodicLatticeShift (wSite 1) (0 : Fin 3)) ≠ thickSlab 2 (wSite 1) := by decide

/-- Thickness `3`: the bond based at `x₀ = 2` crosses. -/
theorem thickSlab3_crossing :
    thickSlab 3 (periodicLatticeShift (wSite 2) (0 : Fin 3)) ≠ thickSlab 3 (wSite 2) := by decide

/-- **THE PRICE IS `2` AT EVERY THICKNESS THE TORUS ADMITS.**  One statement, three covers, one
number — the cube side does not appear in it. -/
theorem slab_price_two_at_every_thickness :
    (∃ γ : Bool → GaugeFn witnessL, PerCubeClass (thickSlab 1) γ (trivialU witnessL) 0
        ∧ 2 ≤ frobSupBond (periodicGaugeTransform (gluedGauge (thickSlab 1) γ)
          (trivialU witnessL)))
    ∧ (∃ γ : Bool → GaugeFn witnessL, PerCubeClass (thickSlab 2) γ (trivialU witnessL) 0
        ∧ 2 ≤ frobSupBond (periodicGaugeTransform (gluedGauge (thickSlab 2) γ)
          (trivialU witnessL)))
    ∧ (∃ γ : Bool → GaugeFn witnessL, PerCubeClass (thickSlab 3) γ (trivialU witnessL) 0
        ∧ 2 ≤ frobSupBond (periodicGaugeTransform (gluedGauge (thickSlab 3) γ)
          (trivialU witnessL))) :=
  ⟨mismatch_price_not_removable (thickSlab 1) (wSite 0, (0 : Fin 3)) thickSlab1_crossing,
   mismatch_price_not_removable (thickSlab 2) (wSite 1, (0 : Fin 3)) thickSlab2_crossing,
   mismatch_price_not_removable (thickSlab 3) (wSite 2, (0 : Fin 3)) thickSlab3_crossing⟩

/-! ## §7 — THE WITNESS: A CURVED BACKGROUND WITH LOAD-BEARING PER-CUBE GAUGES

`CurvedContent.spikeU (torus t)` is the tree's curved, SOURCE-BEARING background on the `4³` torus
(`CurvedContent.spike_is_curved`: nonzero plaquette holonomy and `0 < frobSupBond`, on `0 < t < π`).
The per-cube gauges here are CONSTANT on each of two cubes and DIFFERENT between them, so the family
is genuinely incoherent — `m > 0`, and §6c's collapse does NOT apply to it. -/

/-- The two-cube cover of the `4³` torus: the `x₀ = 0` layer and its complement. -/
def wSlab (x : PeriodicLatticeSite witnessL) : Bool := decide ((x 0 : ℕ) = 0)

/-- Per-cube gauges, constant on each cube and different between them. -/
noncomputable def wGauge (s : ℝ) (i : Bool) : GaugeFn witnessL :=
  fun _ => if i then torus s else 1

/-- `‖torus s − 1‖ ≤ √2·s` on `[0, π]` — `CurvedContent.frobSupBond_spike_le`'s calculus step,
isolated from the lattice so it can be reused for the MISMATCH as well as the radius. -/
theorem frobNorm_torus_sub_one_le {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi) :
    RMapLipschitz.frobNorm ((torus s : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ Real.sqrt 2 * s := by
  rw [frobNorm_torus_sub_one, sqrt_four_one_sub_cos]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h8]
  have hkey := AdalyFormal.Balaban.CurvedContent.two_abs_sin_half_le hs hspi
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hkey, h2]

/-- The same bound at `−s`: `cos` is even, so the mismatch costs the same in both orientations. -/
theorem frobNorm_torus_neg_sub_one_le {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi) :
    RMapLipschitz.frobNorm ((torus (-s) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ Real.sqrt 2 * s := by
  have hcos : Real.cos (-s) = Real.cos s := Real.cos_neg s
  rw [frobNorm_torus_sub_one, hcos, ← frobNorm_torus_sub_one]
  exact frobNorm_torus_sub_one_le hs hspi

/-- **§7a — THE PER-CUBE RADIUS AT A CONSTANT GAUGE IS THE CONFIGURATION'S OWN DEVIATION.**
A constant gauge is a conjugation, so it moves no deviation (`DriftPerCube.frobNorm_constGauge`,
CITED); the class therefore holds at `frobSupBond U_fine` for ANY assignment. -/
theorem perCubeClass_of_constGauges (assign : PeriodicLatticeSite witnessL → Bool) (s : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    PerCubeClass assign (wGauge s) U (frobSupBond U) := by
  intro b
  show RMapLipschitz.frobNorm (((periodicGaugeTransform
    (fun _ => (if assign b.1 then torus s else 1)) U) b :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSupBond U
  rw [frobNorm_constGauge]
  exact frobNorm_le_frobSupBond U b

/-- **§7b — THE MISMATCH OF THE TWO-CUBE FAMILY IS `≤ √2·s`.**  Four cases: equal cubes give `1`
(deviation `0`), and the two crossings give `torus s` and `torus (−s)`. -/
theorem wGauge_mismatch {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi)
    (assign : PeriodicLatticeSite witnessL → Bool) :
    MismatchBound assign (wGauge s) (Real.sqrt 2 * s) := by
  intro b
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 * s := by positivity
  show RMapLipschitz.frobNorm ((((if assign b.1 then torus s else 1)
      * (if assign (periodicLatticeShift b.1 b.2) then torus s else 1)⁻¹ :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ Real.sqrt 2 * s
  by_cases h1 : assign b.1 <;> by_cases h2 : assign (periodicLatticeShift b.1 b.2)
  · rw [if_pos h1, if_pos h2, mul_inv_cancel]
    exact le_of_eq_of_le frobNorm_one_sub_one hnn
  · rw [if_pos h1, if_neg h2, inv_one, mul_one]
    exact frobNorm_torus_sub_one_le hs hspi
  · rw [if_neg h1, if_pos h2, one_mul, torus_inv]
    exact frobNorm_torus_neg_sub_one_le hs hspi
  · rw [if_neg h1, if_neg h2, inv_one, mul_one]
    exact le_of_eq_of_le frobNorm_one_sub_one hnn

/-- **§7c — THE FINE BINDER HOLDS AT A CURVED BACKGROUND WITH TWO DIFFERENT PER-CUBE GAUGES.**
`r = frobSupBond (spikeU (torus t)) ≤ √2·t` and `m ≤ √2·s`; the background is
`CurvedContent.spike_is_curved`'s. -/
theorem fine_binder_at_curved_spike {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    (K : ℝ) (hK : 0 < K) {t s : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi)
    (hs : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hbudget : Real.sqrt 2 * t + Real.sqrt 2 * s ≤ fineRadius ell ell₀ K) :
    K * rawErrorCoeff ell (periodicGaugeTransform (gluedGauge wSlab (wGauge s))
        (AdalyFormal.Balaban.CurvedContent.spikeU (torus t)))
      ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  have hr : frobSupBond (AdalyFormal.Balaban.CurvedContent.spikeU (torus t)) ≤ Real.sqrt 2 * t :=
    AdalyFormal.Balaban.CurvedContent.frobSupBond_spike_le ht htpi
  refine hsmallFineGauged_of_perCube hell hell₀ K hK wSlab (wGauge s) _
    (frobSupBond (AdalyFormal.Balaban.CurvedContent.spikeU (torus t))) (Real.sqrt 2 * s)
    (perCubeClass_of_constGauges wSlab s _) (wGauge_mismatch hs hspi wSlab) ?_
  linarith

/-- **§7d — THE TWO PER-CUBE GAUGES ARE GENUINELY DIFFERENT**, on `0 < s ≤ π`.  So the family is
not a global gauge in disguise and §6c's collapse does not cover it. -/
theorem wGauge_ne {s : ℝ} (hs : 0 < s) (hspi : s ≤ Real.pi) : wGauge s true ≠ wGauge s false := by
  intro hc
  have hval : torus s = 1 := by
    have h0 := congrFun hc (fun _ => (0 : Fin 4))
    simpa [wGauge] using h0
  have hzero : RMapLipschitz.frobNorm ((torus s : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
    rw [hval]
    exact frobNorm_one_sub_one
  rw [frobNorm_torus_sub_one, sqrt_four_one_sub_cos] at hzero
  have hsin : 0 < Real.sin (s / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_of_pos hsin] at hzero
  nlinarith [hzero, h8, hsin]

/-- **§7e — THE WINDOW IS NONEMPTY, IN CLOSED FORM.**  For every scale pair and every `K > 0` there
are `t, s > 0` meeting §7c's budget — so §7c is not a statement about an empty parameter set.  The
witness is explicit: `t = s = min 1 (fineRadius/4)`. -/
theorem fine_witness_window_nonempty {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    {K : ℝ} (hK : 0 < K) :
    ∃ t s : ℝ, 0 < t ∧ t ≤ Real.pi ∧ 0 < s ∧ s ≤ Real.pi
      ∧ Real.sqrt 2 * t + Real.sqrt 2 * s ≤ fineRadius ell ell₀ K := by
  have hR : 0 < fineRadius ell ell₀ K := fineRadius_pos hell hell₀ hK
  set c : ℝ := min 1 (fineRadius ell ell₀ K / 4) with hcdef
  have hc0 : 0 < c := lt_min one_pos (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcR : c ≤ fineRadius ell ell₀ K / 4 := min_le_right _ _
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine ⟨c, c, hc0, le_trans hc1 hpi, hc0, le_trans hc1 hpi, ?_⟩
  nlinarith [hs2, hc0, hcR, Real.sqrt_nonneg 2]

/-! ## §7f — WHY AN END-TO-END INSTANCE OF §5 IS NOT ASSEMBLED HERE, PROVED RATHER THAN ASSERTED

The obvious next step is to instantiate §5 at a fully built datum.  The tree has exactly one:
`DatumWitness.starDatum`, on `ScaleQuotient fineL 2 witnessL` (an `8³` fine torus over the `4³`
coarse one).  `DatumWitness.starDatum_eq_feedDatumGen` (CITED, `rfl`) records what it is built from:

    starDatum bc heps = feedDatumGen starScale (trivialU fineL) heps _

— **its fine background is FLAT.**  §7f shows what that costs: at the one-cube family and the
trivial gauge, BOTH the per-cube radius and the mismatch are exactly `0` and the priced quantity is
exactly `0`, so §5's fine hypothesis there holds for every budget whatsoever and would carry NO
information about the fine background (S82: an algebraically forced assertion is not verification).

**So the missing object is named exactly**: a CURVED `Ufine` on `fineL` together with the
datum-level binders at `feedDatumGen starScale Ufine`.  `CurvedContent`'s curved, source-bearing
background is hard-coded to `witnessL` — the `4³` COARSE torus of this pair — and is not a
configuration on `fineL`, so it cannot be reused for the fine side without being rebuilt there.
§7c above therefore runs the fine binder at a curved background on `witnessL` read as a fine torus
in its own right, which is the strongest non-forced statement the tree's objects support. -/

/-- **THE TREE'S ONLY ASSEMBLED DATUM HAS A FLAT FINE BACKGROUND, AND THERE THE FINE BINDER IS
FORCED.**  Radius `0`, mismatch `0`, priced quantity exactly `0` — for every coefficient `K`,
including `‖H₁‖` at that datum.  This is the reason §7c is stated at a different torus, and it is a
kernel-checked statement rather than a remark. -/
theorem fine_binder_forced_at_flat_fine_background (K : ℝ) :
    PerCubeClass (L := AdalyFormal.DatumWitness.fineL) (fun _ => ())
        (fun _ : Unit => (fun _ => (1 : SU2))) (trivialU AdalyFormal.DatumWitness.fineL) 0
    ∧ MismatchBound (L := AdalyFormal.DatumWitness.fineL) (fun _ => ())
        (fun _ : Unit => (fun _ => (1 : SU2))) 0
    ∧ K * rawErrorCoeff 2 (periodicGaugeTransform
        (gluedGauge (fun _ => ()) (fun _ : Unit => (fun _ => (1 : SU2))))
        (trivialU AdalyFormal.DatumWitness.fineL)) = 0 := by
  have hflat : periodicGaugeTransform
      (gluedGauge (fun _ => ()) (fun _ : Unit => (fun _ => (1 : SU2))))
      (trivialU AdalyFormal.DatumWitness.fineL) = trivialU AdalyFormal.DatumWitness.fineL :=
    AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one _
  have hone : periodicGaugeTransform (fun _ => (1 : SU2))
      (trivialU AdalyFormal.DatumWitness.fineL) = trivialU AdalyFormal.DatumWitness.fineL :=
    AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one _
  refine ⟨?_, mismatchBound_single _, ?_⟩
  · intro b
    show RMapLipschitz.frobNorm (((periodicGaugeTransform (fun _ => (1 : SU2))
      (trivialU AdalyFormal.DatumWitness.fineL)) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 0
    rw [hone]
    exact le_of_eq frobNorm_one_sub_one
  · rw [hflat, AdalyFormal.HrawCarriers.rawErrorCoeff_trivialU, mul_zero]

/-! ## §8 — CONTROLS -/

/-- **THE FACTORISATIONS, IN THE KERNEL.**  Every constant of §3 is `2 ×` a named upstream one or a
product of counted factors; none is fitted. -/
theorem fineRadius_constant_factorisations :
    (338976 : ℝ) = 72 * 4708 ∧ (338976 : ℝ) = 2 * 36 * 4708 ∧ (4708 : ℝ) = 2 * 2354 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **MUST-NOT-HOLD CONTROL — THE RADIUS IS TIGHT.**  Doubling `fineRadius` doubles the priced
quantity EXACTLY, to `2/(4708·ℓ₀³)`, which is strictly larger than the budget.  So no relaxation of
`fineRadius` by any factor `> 1` keeps §3's conclusion, and the constant cannot be loosened. -/
theorem fineRadius_is_tight {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    {K : ℝ} (hK : 0 < K) :
    K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * (2 * fineRadius ell ell₀ K))
      = 2 * (1 / (4708 * (ell₀ : ℝ) ^ 3))
    ∧ 1 / (4708 * (ell₀ : ℝ) ^ 3) < 2 * (1 / (4708 * (ell₀ : ℝ) ^ 3)) := by
  have h2 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
  have hex := fineRadius_prices_exactly hell hell₀ hK
  constructor
  · rw [show (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * (2 * fineRadius ell ell₀ K)
        = 2 * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K) by ring,
      show K * (2 * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K))
        = 2 * (K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * fineRadius ell ell₀ K)) by ring,
      hex]
  · have : (0 : ℝ) < 1 / (4708 * (ell₀ : ℝ) ^ 3) := by positivity
    linarith

/-- **S82 GARBAGE-SUBSTITUTION DISCLOSURE.**  At `r = m = 0` the conclusion of §3 is ALGEBRAICALLY
FORCED — the priced quantity is `0` and any positive budget holds — so that instance carries no
information and is never cited as evidence.  The load-bearing instances are those with `r + m` at
the radius, where `fineRadius_prices_exactly` makes the inequality an equality. -/
theorem fine_price_forced_at_zero {ell ell₀ : ℕ} (hell₀ : 0 < ell₀) (K : ℝ) :
    K * ((36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * (0 + 0)) ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  have h2 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
  have : (0 : ℝ) < 1 / (4708 * (ell₀ : ℝ) ^ 3) := by positivity
  rw [show (0 : ℝ) + 0 = 0 from by norm_num, mul_zero, mul_zero]
  linarith

/-- **THE SCALE TRAP, BOTH DIRECTIONS.**  `ℓ` (RG step) and `ℓ₀` (compression scale) enter
`fineRadius` in DIFFERENT positions — `√ℓ` in the numerator, `ℓ₀³` in the denominator — so the
radius is monotone increasing in `ℓ` and decreasing in `ℓ₀`.  Identifying them is not a harmless
rename, and this states the two monotonicities that a swap would violate. -/
theorem fineRadius_scale_monotonicity {ell ell' ell₀ ell₀' : ℕ} (hell : 0 < ell)
    (hle : ell ≤ ell') (hell₀ : 0 < ell₀) (hle₀ : ell₀ ≤ ell₀') {K : ℝ} (hK : 0 < K) :
    fineRadius ell ell₀ K ≤ fineRadius ell' ell₀ K
      ∧ fineRadius ell ell₀' K ≤ fineRadius ell ell₀ K := by
  have h1 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h2 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
  have h1' : (ell : ℝ) ≤ (ell' : ℝ) := by exact_mod_cast hle
  have h2' : (ell₀ : ℝ) ≤ (ell₀' : ℝ) := by exact_mod_cast hle₀
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hse : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr h1
  have hden : (0 : ℝ) < 338976 * K * (ell₀ : ℝ) ^ 3 := by positivity
  have hnum : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (ell : ℝ) := le_of_lt (mul_pos hs2 hse)
  constructor
  · unfold fineRadius
    gcongr
  · unfold fineRadius
    gcongr

end AdalyFormal.FineDrift
