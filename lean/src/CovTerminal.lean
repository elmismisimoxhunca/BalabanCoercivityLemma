/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovDatum

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# `CovTerminal` — THE DRIFT PRICE IS GAUGE-ORBIT MINIMIZABLE, AND THE TERMINAL THEOREM AT IT

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## §0 — ROW ZERO: EXACTLY WHICH BINDERS SURVIVE

`TerminalBinder.terminal_at_composed_carriers_generalFine` carries FOUR conditions that mention a
background:

| binder | what it says | after this file |
|---|---|---|
| `hsmallU` | `α₁(U) ≤ 1/(13336·ℓ₀³)` — the COARSE half of the drift price `κ` | **gauged**: needed only at ONE point of the gauge orbit (§3) |
| `hsmallFine` | `‖H₁‖·α₁(U_fine)·(36√2/√ℓ) ≤ 1/(2356·ℓ₀³)` — the FINE half of `κ` | **gauged**: needed only at ONE point of the orbit (§3) |
| `hthr` | `α₁(U) ≤ 1/(186·ℓ₀³)` — printed-class membership, feeding the Schur floor | **SURVIVES, and is NOT gauged here.**  In the upstream theorem it is DERIVED from `hsmallU`; once `hsmallU` is gauged it no longer follows, so §4b carries it as an explicit binder.  §5 measures exactly what that costs. |
| `hU`, `hδ` | `LinkDev δ U` and the source threshold | survive unchanged (the dispatch's own list keeps the source threshold) |

**So the honest headline is: the DRIFT binder is gauge invariant; the SCHUR-FLOOR binder `hthr`
is not, and it is the only global-smallness condition on the coarse background left.**  §4a
states the version in which `hsmallU` is kept ungauged — there `hthr` is still derived and the
statement has *no* binder the upstream theorem does not have, while the FINE background is freed
onto its whole gauge orbit.  §4b states the fully gauged version with `hthr` explicit.  Both are
theorems; neither is claimed to be the other.

## §0a — WHY THIS IS NOT `drift_percube`'s `hrough`

`drift_percube` §1(d) (`DriftNoGo.percube_data_cannot_price_the_drift`) proves that the
FLAT-referenced drift is not a function of per-cube gauged data, with a PURE GAUGE witness
`bumpU = 1^{γ₀}` at per-cube radius `0` and `α₁(bumpU) ≥ 2`.  That obstruction is an obstruction to
pricing a GAUGE-VARIANT quantity by GAUGE-INVARIANT data.  §3 removes the variance rather than
fighting it: the price is now evaluated at a gauge of the caller's choosing, so a pure gauge is
priced at its own zero.  `CovWitness.lean` runs exactly that witness.
-/

namespace AdalyFormal.CovariantDatum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeInv gaugeTransform_inv
  gaugeTransform_one)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.TerminalAssembly (IsPrintedG1Form)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawSigmaZero_pos rawErrorCoeff rawErrorCoeff_nonneg)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale dvd_of_scale composedQ feedPen
  coarseSiteEquiv)
open AdalyFormal.TerminalBinder (HrawAt OnMinimizerRange feedDatumGen feedDatumGen_Q
  feedDatumGen_isPrintedG1Form feedDatumGen_hraw_on_range terminal_wired_posDef_on_range
  halfDrift_split thirteen336_strictly_smaller)

variable {L L' : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE COARSE GAUGE FREEDOM IS COMPLETE

`coarseGauge h` is SURJECTIVE onto `GaugeFn L'`: gauging the fine background by an arbitrary `γ`
moves the coarse background by an ARBITRARY coarse gauge.  Without this, §3's coarse-side freedom
could be a sliver of the coarse gauge group (a free-parameter/vacuity trap: the quantifier would
range over a set nobody had measured). -/

open Classical in
/-- A fine gauge realising a prescribed coarse gauge: `γ'` at block corners, `1` elsewhere. -/
noncomputable def liftCoarseGauge (h : ScaleQuotient L ell L') (γ' : GaugeFn L') : GaugeFn L :=
  fun x => if hx : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell then
    γ' (coarseSiteEquiv h ⟨x, hx⟩) else 1

theorem coarseGauge_liftCoarseGauge (h : ScaleQuotient L ell L') (γ' : GaugeFn L') :
    coarseGauge h (liftCoarseGauge h γ') = γ' := by
  funext z
  show (if hx : (((coarseSiteEquiv h).symm z).1)
      ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell then
      γ' (coarseSiteEquiv h ⟨((coarseSiteEquiv h).symm z).1, hx⟩) else 1) = γ' z
  rw [dif_pos ((coarseSiteEquiv h).symm z).2]
  congr 1
  rw [show (⟨((coarseSiteEquiv h).symm z).1, ((coarseSiteEquiv h).symm z).2⟩ :
      {y : PeriodicLatticeSite L // y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell})
    = (coarseSiteEquiv h).symm z from rfl]
  exact (coarseSiteEquiv h).apply_symm_apply z

/-- **THE COARSE GAUGE GROUP IS REACHED IN FULL.** -/
theorem coarseGauge_surjective (h : ScaleQuotient L ell L') :
    Function.Surjective (coarseGauge (L := L) (L' := L') (ell := ell) h) :=
  fun γ' => ⟨liftCoarseGauge h γ', coarseGauge_liftCoarseGauge h γ'⟩

/-! ## §2 — `HrawAt` TRANSPORTS ALONG THE GAUGE ORBIT, WITH THE SAME CONSTANTS -/

/-- **THE TRANSPORT IDENTITY.**  `hraw` at the gauged pair, evaluated at the gauged vector, IS
`hraw` at the original pair evaluated at the original vector — the three quantities it compares are
gauge invariants of the covariant datum (`CovGauge` §1c, §2; `CovDatum` §4d). -/
theorem hrawAt_gauge_iff (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (σ₀ κ : ℝ) (A : BondFnL2 L) :
    HrawAt (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha)
        (periodicGaugeTransform (coarseGauge h γ) U)
        (curlCovariantCLM_L2 (periodicGaugeTransform γ Ufine)) σ₀ κ (gaugeL2 γ A)
      ↔ HrawAt (feedDatumGen h Ufine heps ha) U (curlCovariantCLM_L2 Ufine) σ₀ κ A := by
  unfold HrawAt
  rw [feedDatumGen_Q_gauge h γ Ufine heps ha A,
    norm_curl_gaugeL2 (coarseGauge h γ) U ((feedDatumGen h Ufine heps ha).Q A),
    norm_gaugeL2, norm_curl_gaugeL2 γ Ufine A]

/-! ## §3 — THE DRIFT PRICE, EVALUATED ANYWHERE ON THE GAUGE ORBIT -/

/-- **THE GAUGED DRIFT PRICE.**  `κ_γ := 4√2·α₁(U^{γ̄}) + ‖H₁‖·(36√2/√ℓ)·α₁(U_fine^γ)`, with
`‖H₁‖` measured at the ORIGINAL fine background — legitimate because `CovDatum` §4f proves
`‖H₁‖` is a gauge invariant, so no `γ` appears in that factor. -/
noncomputable def gaugedKappa (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) : ℝ :=
  4 * Real.sqrt 2 * frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
    + ‖solutionOperator (feedDatumGen h Ufine heps ha)‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine)

theorem gaugedKappa_nonneg (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    0 ≤ gaugedKappa h γ Ufine U heps ha := by
  unfold gaugedKappa
  have h1 : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond (periodicGaugeTransform (coarseGauge h γ) U) :=
    mul_nonneg (by positivity) (frobSupBond_nonneg _)
  have h2 : (0 : ℝ) ≤ ‖solutionOperator (feedDatumGen h Ufine heps ha)‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) :=
    mul_nonneg (norm_nonneg _) (rawErrorCoeff_nonneg _ _)
  linarith

/-- **THE HEADLINE OF THIS FILE.**  At the covariant datum, `hraw` holds on the minimiser range
with the drift price measured AT AN ARBITRARY POINT OF THE GAUGE ORBIT of the pair
`(U_fine, U)` — one gauge `γ` on the fine torus, moving the coarse background by the induced
`γ̄` (which §1 shows is an arbitrary coarse gauge).

`γ = 1` recovers `TerminalBinder.feedDatumGen_hraw_on_range` exactly (`gaugeTransform_one`), so
nothing is lost; every other `γ` is new. -/
theorem hraw_on_range_gauged (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    OnMinimizerRange (feedDatumGen h Ufine heps ha)
      (HrawAt (feedDatumGen h Ufine heps ha) U (curlCovariantCLM_L2 Ufine) (rawSigmaZero ell)
        (gaugedKappa h γ Ufine U heps ha)) := by
  intro B
  -- the gauged datum's own `hraw`, at the gauged coarse background, evaluated at `Ḡ B`
  have hg := feedDatumGen_hraw_on_range h (periodicGaugeTransform γ Ufine) heps ha
    (periodicGaugeTransform (coarseGauge h γ) U) (gaugeL2 (coarseGauge h γ) B)
  -- `‖H₁‖` is a gauge invariant, so the price is the one `gaugedKappa` names
  rw [norm_solutionOperator_feedDatumGen_gauge h γ Ufine heps ha] at hg
  -- and the minimiser transports
  rw [feedDatumGen_solutionOperator_gauge h γ Ufine heps ha B] at hg
  exact (hrawAt_gauge_iff h γ Ufine U heps ha (rawSigmaZero ell)
    (gaugedKappa h γ Ufine U heps ha) (solutionOperator (feedDatumGen h Ufine heps ha) B)).mp hg

/-- **NOTHING IS LOST AT `γ = 1`** — the trivial gauge returns the upstream price verbatim.  This
is the control that `hraw_on_range_gauged` is a genuine extension and not a re-statement at some
other point. -/
theorem gaugedKappa_at_one (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    gaugedKappa h (fun _ => (1 : SU2)) Ufine U heps ha
      = 4 * Real.sqrt 2 * frobSupBond U
        + ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ * rawErrorCoeff ell Ufine := by
  unfold gaugedKappa
  rw [gaugeTransform_one]
  have hcoarse : coarseGauge h (fun _ => (1 : SU2)) = fun _ => (1 : SU2) := rfl
  rw [hcoarse, gaugeTransform_one]

/-! ## §4 — THE TERMINAL THEOREM AT THE COVARIANT DATUM -/

/-- **§4a — THE FINE BACKGROUND IS FREED ONTO ITS WHOLE GAUGE ORBIT, AT NO COST IN BINDERS.**

Binder for binder `TerminalBinder.terminal_at_composed_carriers_generalFine`, except that

    hsmallFine : ‖H₁‖ · rawErrorCoeff ℓ U_fine ≤ 1/(2356·ℓ₀³)

— a condition on `U_fine` ITSELF — is replaced by the same condition at `U_fine^γ` for a gauge `γ`
of the caller's choosing, with `γ̄ = 1` (so the coarse background is untouched and `hthr` is still
DERIVED from `hsmallU`, exactly as upstream).  No binder is added and none is weakened elsewhere.

A fine background that is a pure gauge, or any gauge transform of a small one, is admitted here and
is NOT admitted upstream. -/
theorem terminal_covariant_fineGauged {ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ : GaugeFn L) (hγcoarse : coarseGauge h γ = fun _ => (1 : SU2))
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallU : frobSupBond U ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFineGauged : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3))
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
  have hκ0 := gaugedKappa_nonneg h γ Ufine U heps (le_of_lt bc.a_pos)
  have hcoarseU : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U) = frobSupBond U := by
    rw [hγcoarse, gaugeTransform_one]
  have hhalf : gaugedKappa h γ Ufine U heps (le_of_lt bc.a_pos)
      ≤ Real.sqrt (gammaBrick ell₀) / 2 := by
    unfold gaugedKappa
    rw [hcoarseU]
    exact halfDrift_split hell _ _ (frobSupBond_nonneg U) hsmallU hsmallFineGauged
  exact terminal_wired_posDef_on_range hell2 hstrict hdvd0 U hthr
    (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc (curlCovariantCLM_L2 Ufine)
    (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L)
    (rawSigmaZero ell) _ (rawSigmaZero_pos (ell_pos_of_scale h)) hκ0 hhalf
    (fun B => feedDatumGen_isPrintedG1Form h Ufine heps (le_of_lt bc.a_pos) _)
    (hraw_on_range_gauged h γ Ufine U heps (le_of_lt bc.a_pos))
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

/-- **§4b — BOTH BACKGROUNDS FREED ONTO THE JOINT GAUGE ORBIT.**

Here BOTH halves of the drift price are measured at `γ` — so `U` itself may be arbitrarily far from
`1` provided SOME point of its coarse gauge orbit is small.  The price is stated in row zero and is
not hidden: `hthr` is now an explicit binder, because it no longer follows from `hsmallU` (which is
gone).  Nothing else changes. -/
theorem terminal_covariant_bothGauged {ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (γ : GaugeFn L)
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmallUGauged : frobSupBond (periodicGaugeTransform (coarseGauge h γ) U)
      ≤ 1 / (13336 * (ell₀ : ℝ) ^ 3))
    (hthr : frobSupBond U ≤ 1 / (186 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hsmallFineGauged : ‖solutionOperator (feedDatumGen h Ufine heps (le_of_lt bc.a_pos))‖
      * rawErrorCoeff ell (periodicGaugeTransform γ Ufine) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3))
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
  have hκ0 := gaugedKappa_nonneg h γ Ufine U heps (le_of_lt bc.a_pos)
  have hhalf : gaugedKappa h γ Ufine U heps (le_of_lt bc.a_pos)
      ≤ Real.sqrt (gammaBrick ell₀) / 2 :=
    halfDrift_split hell _ _ (frobSupBond_nonneg _) hsmallUGauged hsmallFineGauged
  exact terminal_wired_posDef_on_range hell2 hstrict hdvd0 U hthr
    (feedDatumGen h Ufine heps (le_of_lt bc.a_pos)) bc (curlCovariantCLM_L2 Ufine)
    (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L)
    (rawSigmaZero ell) _ (rawSigmaZero_pos (ell_pos_of_scale h)) hκ0 hhalf
    (fun B => feedDatumGen_isPrintedG1Form h Ufine heps (le_of_lt bc.a_pos) _)
    (hraw_on_range_gauged h γ Ufine U heps (le_of_lt bc.a_pos))
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

end AdalyFormal.CovariantDatum
