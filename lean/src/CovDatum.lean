/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovGauge

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# `CovDatum` — THE COVARIANT DATUM IS GAUGE EQUIVARIANT, FIELD BY FIELD

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## What is proved

`feedDatumGen h U_fine ε a` is the datum whose constraint operator is the COVARIANT coarse
restriction `composedQ h U_fine` (`qCLM U_fine`, i.e. `LineIntegralCovariant.lineCoarseRestrictCov`
at the SAME background) and whose printed `d` is the COVARIANT curl `curlCovariantCLM_L2 U_fine` —
so the flat anchors of `HrawFeed.feedDatum` (`composedQ h (trivialU L)`, `d = curl₁`) are already
gone from the DEFINITION.  What did not exist is the statement that the assembled object
TRANSFORMS.  §3 supplies it:

    Ginv, Gstar, Q, Qstar, Comp, CompInv, H₁   at   U_fine^γ
      =   G_γ ∘ (same at U_fine) ∘ G_γ⁻¹      (coarse slots conjugated by G_{γ̄})

for an ARBITRARY gauge `γ`, and hence `‖H₁‖` is a gauge INVARIANT (§3f).

## Two methodological notes

1. **The `Ginv` intertwining is proved by POLARIZATION, not by opening `dstarDCLM`.**  §2 proves
   that a self-adjoint operator is determined by its quadratic form; §3a proves the quadratic
   forms agree (three gauge-invariant norms, `CovGauge` §1b/§1c/§2); §3b concludes the operator
   identity.  Nothing in this file depends on how `dstarDCLM` is built.
2. **`Gstar`, `Qstar`, `Comp`, `CompInv` are OPAQUE FIELDS of the structure** — they are not
   definable from `Ginv` and `Q` inside the datum.  They are pinned by UNIQUENESS (§2a: a
   two-sided inverse is unique; §3c: an adjoint is unique), so the equivariance is forced rather
   than assumed.  This is why §3 is stated for two ARBITRARY data related by isometries
   (`covData_conj_*`) and only then instantiated: no field of `build` is unfolded anywhere.
-/

namespace AdalyFormal.CovariantDatum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply interpolates)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeInv gaugeTransform_inv)
open AdalyFormal.HrawCarriers (ScaleQuotient composedQ)
open AdalyFormal.TerminalBinder (feedGinvGen inner_feedGinvGen feedGinvGen_selfAdjoint
  feedDatumGen feedDatumGen_Q feedDatumGen_Ginv)

variable {L L' : PeriodicLatticeExtent}

/-! ## §2 — TWO UNIQUENESS FACTS, AND POLARIZATION -/

/-- **A two-sided inverse is unique.**  Used three times: for `Gstar` (§3b), for `CompInv` (§3e),
and nowhere else.  Elementary, and stated on bare functions so no algebraic structure is needed. -/
theorem twoSided_inverse_unique {X : Type*} (f g g' : X → X)
    (hfg : ∀ x, f (g x) = x) (hg'f : ∀ x, g' (f x) = x) : ∀ x, g x = g' x := by
  intro x
  calc g x = g' (f (g x)) := (hg'f (g x)).symm
    _ = g' x := by rw [hfg x]

/-- **A self-adjoint operator is determined by its quadratic form** (real polarization).
`⟪x+y, T(x+y)⟫ − ⟪x−y, T(x−y)⟫ = 4⟪x, T y⟫`. -/
theorem selfAdjoint_polarization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (hsa : ∀ x y : H, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y)) (x y : H) :
    (inner ℝ (x + y) (T (x + y)) : ℝ) - (inner ℝ (x - y) (T (x - y)) : ℝ)
      = 4 * (inner ℝ x (T y) : ℝ) := by
  have hsym : (inner ℝ y (T x) : ℝ) = inner ℝ x (T y) := by
    rw [← hsa x y, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [hsym]
  ring

/-! ## §3 — EQUIVARIANCE FOR AN ARBITRARY PAIR OF CONJUGATE DATA

Stated for two abstract data related by isometry equivalences, so that §4's instantiation cannot
smuggle in anything about `build`. -/

section Conj

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- `Gstar` conjugates, forced by uniqueness of the two-sided inverse. -/
theorem covData_conj_Gstar (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H)
    (hGinv : ∀ x, D₂.Ginv (G x) = G (D₁.Ginv x)) (y : H) :
    D₂.Gstar (G y) = G (D₁.Gstar y) := by
  have key : D₂.Ginv (G (D₁.Gstar y)) = G y := by
    rw [hGinv, D₁.Ginv_Gstar]
  calc D₂.Gstar (G y) = D₂.Gstar (D₂.Ginv (G (D₁.Gstar y))) := by rw [key]
    _ = G (D₁.Gstar y) := D₂.Gstar_Ginv _

/-- `Qstar` conjugates, forced by uniqueness of the adjoint (nondegeneracy of the inner product). -/
theorem covData_conj_Qstar (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H) (Gbar : K ≃ₗᵢ[ℝ] K)
    (hQ : ∀ x, D₂.Q (G x) = Gbar (D₁.Q x)) (w : K) :
    D₂.Qstar (Gbar w) = G (D₁.Qstar w) := by
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨y, rfl⟩ : ∃ y, G y = v := ⟨G.symm v, G.apply_symm_apply v⟩
  calc (inner ℝ (G y) (D₂.Qstar (Gbar w)) : ℝ)
      = inner ℝ (D₂.Q (G y)) (Gbar w) := (D₂.Q_Qstar_adjoint (G y) (Gbar w)).symm
    _ = inner ℝ (Gbar (D₁.Q y)) (Gbar w) := by rw [hQ]
    _ = inner ℝ (D₁.Q y) w := Gbar.inner_map_map _ _
    _ = inner ℝ y (D₁.Qstar w) := D₁.Q_Qstar_adjoint y w
    _ = inner ℝ (G y) (G (D₁.Qstar w)) := (G.inner_map_map _ _).symm

/-- `Comp = Q G_* Q^*` conjugates on the coarse side. -/
theorem covData_conj_Comp (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H) (Gbar : K ≃ₗᵢ[ℝ] K)
    (hGinv : ∀ x, D₂.Ginv (G x) = G (D₁.Ginv x)) (hQ : ∀ x, D₂.Q (G x) = Gbar (D₁.Q x)) (w : K) :
    D₂.Comp (Gbar w) = Gbar (D₁.Comp w) := by
  rw [D₂.Comp_eq, covData_conj_Qstar D₁ D₂ G Gbar hQ w,
    covData_conj_Gstar D₁ D₂ G hGinv (D₁.Qstar w), hQ, ← D₁.Comp_eq]

/-- `CompInv` conjugates, forced again by uniqueness of the two-sided inverse. -/
theorem covData_conj_CompInv (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H)
    (Gbar : K ≃ₗᵢ[ℝ] K) (hGinv : ∀ x, D₂.Ginv (G x) = G (D₁.Ginv x))
    (hQ : ∀ x, D₂.Q (G x) = Gbar (D₁.Q x)) (w : K) :
    D₂.CompInv (Gbar w) = Gbar (D₁.CompInv w) := by
  have key : D₂.Comp (Gbar (D₁.CompInv w)) = Gbar w := by
    rw [covData_conj_Comp D₁ D₂ G Gbar hGinv hQ, D₁.Comp_CompInv]
  calc D₂.CompInv (Gbar w) = D₂.CompInv (D₂.Comp (Gbar (D₁.CompInv w))) := by rw [key]
    _ = Gbar (D₁.CompInv w) := D₂.CompInv_Comp _

/-- **THE SOLUTION OPERATOR CONJUGATES**: `H₁(D₂)(Ḡ w) = G (H₁(D₁) w)`. -/
theorem covData_conj_solutionOperator (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H)
    (Gbar : K ≃ₗᵢ[ℝ] K) (hGinv : ∀ x, D₂.Ginv (G x) = G (D₁.Ginv x))
    (hQ : ∀ x, D₂.Q (G x) = Gbar (D₁.Q x)) (w : K) :
    solutionOperator D₂ (Gbar w) = G (solutionOperator D₁ w) := by
  rw [solutionOperator_apply, solutionOperator_apply,
    covData_conj_CompInv D₁ D₂ G Gbar hGinv hQ w,
    covData_conj_Qstar D₁ D₂ G Gbar hQ (D₁.CompInv w),
    covData_conj_Gstar D₁ D₂ G hGinv]

/-- **`‖H₁‖` IS A CONJUGATION INVARIANT.**  Both inequalities from the same identity; no operator
norm of `G` is ever needed, only that it is an isometry EQUIVALENCE. -/
theorem covData_conj_norm_solutionOperator (D₁ D₂ : BalabanCovarianceData H K) (G : H ≃ₗᵢ[ℝ] H)
    (Gbar : K ≃ₗᵢ[ℝ] K) (hGinv : ∀ x, D₂.Ginv (G x) = G (D₁.Ginv x))
    (hQ : ∀ x, D₂.Q (G x) = Gbar (D₁.Q x)) :
    ‖solutionOperator D₂‖ = ‖solutionOperator D₁‖ := by
  have hconj := covData_conj_solutionOperator D₁ D₂ G Gbar hGinv hQ
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun B => ?_)
    have hB : Gbar (Gbar.symm B) = B := Gbar.apply_symm_apply B
    calc ‖solutionOperator D₂ B‖ = ‖solutionOperator D₂ (Gbar (Gbar.symm B))‖ := by rw [hB]
      _ = ‖G (solutionOperator D₁ (Gbar.symm B))‖ := by rw [hconj]
      _ = ‖solutionOperator D₁ (Gbar.symm B)‖ := G.norm_map _
      _ ≤ ‖solutionOperator D₁‖ * ‖Gbar.symm B‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖solutionOperator D₁‖ * ‖B‖ := by rw [Gbar.symm.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun w => ?_)
    calc ‖solutionOperator D₁ w‖ = ‖G (solutionOperator D₁ w)‖ := (G.norm_map _).symm
      _ = ‖solutionOperator D₂ (Gbar w)‖ := by rw [hconj]
      _ ≤ ‖solutionOperator D₂‖ * ‖Gbar w‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖solutionOperator D₂‖ * ‖w‖ := by rw [Gbar.norm_map]

/-- **THE `Ginv` INTERTWINING FROM THE QUADRATIC FORM ALONE** (polarization).  This is what lets
§4 avoid unfolding `dstarDCLM`. -/
theorem ginv_conj_of_quadForm (T₁ T₂ : H →L[ℝ] H) (G : H ≃ₗᵢ[ℝ] H)
    (hsa₁ : ∀ x y : H, (inner ℝ (T₁ x) y : ℝ) = inner ℝ x (T₁ y))
    (hsa₂ : ∀ x y : H, (inner ℝ (T₂ x) y : ℝ) = inner ℝ x (T₂ y))
    (hq : ∀ x : H, (inner ℝ (G x) (T₂ (G x)) : ℝ) = inner ℝ x (T₁ x)) (x : H) :
    T₂ (G x) = G (T₁ x) := by
  -- bilinear version of `hq`, by polarization on both sides
  have hbil : ∀ u v : H, (inner ℝ (G u) (T₂ (G v)) : ℝ) = inner ℝ u (T₁ v) := by
    intro u v
    have h4 : (4 : ℝ) * (inner ℝ (G u) (T₂ (G v)) : ℝ) = 4 * (inner ℝ u (T₁ v) : ℝ) := by
      have e2 := selfAdjoint_polarization T₂ hsa₂ (G u) (G v)
      have e1 := selfAdjoint_polarization T₁ hsa₁ u v
      have hadd : G u + G v = G (u + v) := (G.map_add u v).symm
      have hsub : G u - G v = G (u - v) := (G.map_sub u v).symm
      rw [hadd, hsub, hq (u + v), hq (u - v)] at e2
      rw [e1] at e2
      exact e2.symm
    linarith
  refine ext_inner_left ℝ (fun w => ?_)
  obtain ⟨u, rfl⟩ : ∃ u, G u = w := ⟨G.symm w, G.apply_symm_apply w⟩
  rw [hbil u x, ← G.inner_map_map u (T₁ x)]

end Conj

/-! ## §4 — INSTANTIATION AT THE COVARIANT DATUM -/

variable {ell : ℕ}

/-- **§4a — THE QUADRATIC FORM OF `G₁⁻¹` IS A GAUGE INVARIANT.**  All three summands are:
the covariant curl's norm (`norm_curl_gaugeL2`), the bond norm (`norm_gaugeL2`), and the covariant
`Q`'s norm (`norm_composedQ_gauge`).  The `ε` slot is invariant because the gauge action is an
ISOMETRY — this is where `ε > 0` and covariance are checked to be compatible. -/
theorem feedGinvGen_quadForm_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (A : BondFnL2 L) :
    (inner ℝ (gaugeL2 γ A)
        (feedGinvGen h (periodicGaugeTransform γ Ufine) eps a (gaugeL2 γ A)) : ℝ)
      = inner ℝ A (feedGinvGen h Ufine eps a A) := by
  rw [inner_feedGinvGen, inner_feedGinvGen, norm_curl_gaugeL2, norm_gaugeL2,
    norm_composedQ_gauge]

/-- **§4b — `G₁⁻¹` INTERTWINES** with the gauge action, at an ARBITRARY gauge. -/
theorem feedGinvGen_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (A : BondFnL2 L) :
    feedGinvGen h (periodicGaugeTransform γ Ufine) eps a (gaugeL2 γ A)
      = gaugeL2 γ (feedGinvGen h Ufine eps a A) :=
  ginv_conj_of_quadForm (feedGinvGen h Ufine eps a)
    (feedGinvGen h (periodicGaugeTransform γ Ufine) eps a) (gaugeL2 γ)
    (feedGinvGen_selfAdjoint h Ufine eps a)
    (feedGinvGen_selfAdjoint h (periodicGaugeTransform γ Ufine) eps a)
    (feedGinvGen_quadForm_gauge h γ Ufine eps a) A

/-- **§4c — THE DATUM'S `Ginv` SLOT INTERTWINES.** -/
theorem feedDatumGen_Ginv_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (A : BondFnL2 L) :
    (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha).Ginv (gaugeL2 γ A)
      = gaugeL2 γ ((feedDatumGen h Ufine heps ha).Ginv A) := by
  rw [feedDatumGen_Ginv h (periodicGaugeTransform γ Ufine) heps ha,
    feedDatumGen_Ginv h Ufine heps ha]
  exact feedGinvGen_gauge h γ Ufine eps a A

/-- **§4d — THE DATUM'S `Q` SLOT INTERTWINES**, with the coarse slot conjugated by the INDUCED
coarse gauge `γ̄` (`CovGauge.coarseGauge`), not by an independently chosen one. -/
theorem feedDatumGen_Q_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (A : BondFnL2 L) :
    (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha).Q (gaugeL2 γ A)
      = gaugeL2 (coarseGauge h γ) ((feedDatumGen h Ufine heps ha).Q A) := by
  rw [feedDatumGen_Q h (periodicGaugeTransform γ Ufine) heps ha, feedDatumGen_Q h Ufine heps ha]
  exact composedQ_gauge h γ Ufine A

/-- **§4e — THE ASSEMBLED DATUM IS GAUGE EQUIVARIANT: THE SOLUTION OPERATOR CONJUGATES.** -/
theorem feedDatumGen_solutionOperator_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) (B : BondFnL2 L') :
    solutionOperator (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha)
        (gaugeL2 (coarseGauge h γ) B)
      = gaugeL2 γ (solutionOperator (feedDatumGen h Ufine heps ha) B) :=
  covData_conj_solutionOperator (feedDatumGen h Ufine heps ha)
    (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha) (gaugeL2 γ)
    (gaugeL2 (coarseGauge h γ))
    (feedDatumGen_Ginv_gauge h γ Ufine heps ha) (feedDatumGen_Q_gauge h γ Ufine heps ha) B

/-- **§4f — AND THEREFORE `‖H₁‖` IS A GAUGE INVARIANT OF THE COVARIANT DATUM.**  This is the fact
that makes the fine half of the drift price gaugeable: `hsmallFine` reads `‖H₁‖ · α₁(U_fine)`, and
only the SECOND factor moves under a gauge. -/
theorem norm_solutionOperator_feedDatumGen_gauge (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a) :
    ‖solutionOperator (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha)‖
      = ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ :=
  covData_conj_norm_solutionOperator (feedDatumGen h Ufine heps ha)
    (feedDatumGen h (periodicGaugeTransform γ Ufine) heps ha) (gaugeL2 γ)
    (gaugeL2 (coarseGauge h γ))
    (feedDatumGen_Ginv_gauge h γ Ufine heps ha) (feedDatumGen_Q_gauge h γ Ufine heps ha)

/-! ## §5 — `Q` IS STILL GENUINELY NON-INJECTIVE AT THE COVARIANT CARRIER

S82/vacuity trap 2 of the dispatch: the carrier changed, so this is RE-PROVED at the covariant
datum rather than inherited from the flat one.  `TerminalBinder.feedDatumGen_Q_not_injective` is
the general-fine statement and is CITED; §5a records that the gauge action does not repair
injectivity either — the kernel is transported, not shrunk. -/

/-- **The kernel of the covariant `Q` transports under gauges and stays nontrivial.**  If `A ≠ 0`
lies in `ker Q(U_fine)`, then `A^γ ≠ 0` lies in `ker Q(U_fine^γ)`: non-injectivity is a gauge
invariant, so no choice of gauge can make the covariant constraint operator injective. -/
theorem kernel_transports (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) (hA : A ≠ 0) (hker : composedQ h Ufine A = 0) :
    gaugeL2 γ A ≠ 0 ∧ composedQ h (periodicGaugeTransform γ Ufine) (gaugeL2 γ A) = 0 := by
  constructor
  · intro hz
    exact hA (by simpa using (gaugeL2 γ).injective (by rw [hz]; exact (map_zero _).symm))
  · rw [composedQ_gauge, hker, map_zero]

end AdalyFormal.CovariantDatum
