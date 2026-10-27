/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CovTerminal
import DriftNoGo

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# `CovWitness` — THE GAUGE QUANTIFIER IS LOAD-BEARING, MEASURED

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

`CovTerminal` §4a's fine-background hypothesis is `hsmallFineGauged`, evaluated at `U_fine^γ`.
If that were satisfiable only when `U_fine` itself is already small, the gauge quantifier would be
decoration.  This file exhibits a fine background where the two differ by a factor `≥ 2`:

* `spikeU g x₀ := 1^{γ}` with `γ = spikeGauge g x₀` (`AlphaAnalyticity`, REUSED) — a PURE GAUGE;
* at `g = witnessMElem = !![0,1;−1,0]` its own deviation is `α₁ ≥ 2` (§2), so the UNGAUGED
  hypothesis `hsmallFine` forces `‖H₁‖ ≤ √ℓ/(169632√2·ℓ₀³)` — an explicit smallness on the
  solution operator that has nothing to do with the background (§4);
* while the GAUGED hypothesis holds at `γ⁻¹` with the error coefficient EXACTLY `0` (§3), for
  every `‖H₁‖` whatsoever;
* and when `x₀` is not a block corner the induced coarse gauge is trivial (§3a), so §4a applies
  verbatim with the coarse background untouched.

This is `drift_percube`'s own no-go witness (`DriftNoGo`, whose `bumpU` is the same construction at
`witnessL`) read from the other side: that lane proves a pure gauge cannot be priced by the
FLAT-referenced drift; here the reference moves with the gauge, and the same configuration is
priced at its own zero.
-/

namespace AdalyFormal.CovariantDatum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  interpolates)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 witnessMElem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeInv gaugeTransform_inv
  gaugeTransform_one spikeGauge spikeGauge_at)
open AdalyFormal.Balaban.DriftPerCube (pureGauge pureGauge_apply pureGauge_one
  frobNorm_witnessM_sub_one)
open AdalyFormal.MechEdges.G16 (rawSigmaZero rawErrorCoeff rawErrorCoeff_nonneg)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale coarseSiteEquiv composedQ
  rawErrorCoeff_trivialU)
open AdalyFormal.TerminalBinder (feedDatumGen feedDatumGen_Q feedGinvGen inner_feedGinvGen)

variable {L L' : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE PURE-GAUGE WITNESS, GENERAL IN `L` AND IN THE SPIKE SITE -/

/-- **The pure gauge of a one-site spike**: `1^{γ}` with `γ = g` at `x₀` and `1` elsewhere.  Built
from the tree's own `spikeGauge` and `DriftPerCube.pureGauge`; nothing new is defined. -/
noncomputable def spikeU (g : SU2) (x₀ : PeriodicLatticeSite L) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  pureGauge (spikeGauge g x₀)

/-- **THE WITNESS IS UNDONE BY ONE GAUGE**: `(1^γ)^{γ⁻¹} = 1`, exactly. -/
theorem spikeU_gauged_flat (g : SU2) (x₀ : PeriodicLatticeSite L) :
    periodicGaugeTransform (gaugeInv (spikeGauge g x₀)) (spikeU g x₀) = trivialU L :=
  gaugeTransform_inv (spikeGauge g x₀) (trivialU L)

/-- A forward step leaves its own site whenever the torus has side `> 1` in that direction. -/
theorem shift_ne_self (x : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    periodicLatticeShift x μ ≠ x := by
  intro hc
  have hμ : (Function.update x μ (x μ + 1)) μ = x μ := congrFun hc μ
  rw [Function.update_self] at hμ
  have h10 : (1 : Fin (L μ + 1)) = 0 := by
    have := hμ
    nth_rewrite 2 [show x μ = x μ + 0 from (add_zero _).symm] at this
    exact add_left_cancel this
  have hval : ((1 : Fin (L μ + 1)) : ℕ) = ((0 : Fin (L μ + 1)) : ℕ) := congrArg Fin.val h10
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
  exact absurd hval (by omega)

/-- **THE WITNESS'S LINK AT THE SPIKE SITE IS `g`.** -/
theorem spikeU_at (g : SU2) (x₀ : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    spikeU g x₀ (x₀, μ) = g := by
  show pureGauge (spikeGauge g x₀) (x₀, μ) = g
  rw [pureGauge_apply]
  show spikeGauge g x₀ x₀ * (spikeGauge g x₀ (periodicLatticeShift x₀ μ))⁻¹ = g
  rw [spikeGauge_at,
    show spikeGauge g x₀ (periodicLatticeShift x₀ μ) = 1 from if_neg (shift_ne_self x₀ μ hL),
    inv_one, mul_one]

/-! ## §2 — ITS OWN DEVIATION IS `≥ 2` -/

/-- **`α₁(spikeU witnessMElem x₀) ≥ 2`.**  One bond suffices; `frobNorm(witnessMElem − 1) = 2` is
`DriftPerCube`'s own computation, CITED. -/
theorem two_le_frobSupBond_spikeU (x₀ : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    2 ≤ frobSupBond (spikeU witnessMElem x₀) := by
  have h := frobNorm_le_frobSupBond (spikeU witnessMElem x₀) (x₀, μ)
  rwa [spikeU_at witnessMElem x₀ μ hL, frobNorm_witnessM_sub_one] at h

/-! ## §3 — THE GAUGED HYPOTHESIS HOLDS AT RADIUS EXACTLY ZERO -/

/-- **The gauged error coefficient VANISHES**: `rawErrorCoeff ℓ ((1^γ)^{γ⁻¹}) = 0`. -/
theorem rawErrorCoeff_spikeU_gauged (g : SU2) (x₀ : PeriodicLatticeSite L) :
    rawErrorCoeff ell (periodicGaugeTransform (gaugeInv (spikeGauge g x₀)) (spikeU g x₀)) = 0 := by
  rw [spikeU_gauged_flat, rawErrorCoeff_trivialU]

/-- **`CovTerminal` §4a's FINE HYPOTHESIS HOLDS AT THE WITNESS, FOR EVERY `‖H₁‖`.** -/
theorem hsmallFineGauged_at_spikeU {ell₀ : ℕ} (hell₀ : 0 < ell₀) (K : ℝ)
    (g : SU2) (x₀ : PeriodicLatticeSite L) :
    K * rawErrorCoeff ell (periodicGaugeTransform (gaugeInv (spikeGauge g x₀)) (spikeU g x₀))
      ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell₀
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  rw [rawErrorCoeff_spikeU_gauged, mul_zero]
  positivity

/-! ### §3a — AND THE INDUCED COARSE GAUGE IS TRIVIAL WHEN THE SPIKE IS NOT A BLOCK CORNER -/

/-- If the spike site is not in the coarse lattice, the gauge that undoes the witness induces the
IDENTITY on the coarse torus, so `CovTerminal.terminal_covariant_fineGauged`'s `hγcoarse` holds and
the coarse background is untouched. -/
theorem coarseGauge_spikeInv_trivial (h : ScaleQuotient L ell L') (g : SU2)
    (x₀ : PeriodicLatticeSite L) (hx₀ : x₀ ∉ CoarseLattice L ell) :
    coarseGauge h (gaugeInv (spikeGauge g x₀)) = fun _ => (1 : SU2) := by
  funext z
  show (spikeGauge g x₀ (((coarseSiteEquiv h).symm z).1))⁻¹ = 1
  have hne : (((coarseSiteEquiv h).symm z).1) ≠ x₀ := by
    intro hc
    exact hx₀ (hc ▸ ((coarseSiteEquiv h).symm z).2)
  rw [show spikeGauge g x₀ (((coarseSiteEquiv h).symm z).1) = 1 from if_neg hne, inv_one]

/-! ## §4 — THE SEPARATION, IN EXACT ARITHMETIC

What the UNGAUGED hypothesis costs at this background.  `rawErrorCoeff ℓ U = (36√2/√ℓ)·α₁(U)` and
`α₁ ≥ 2` (§2), so `hsmallFine` at the witness is a bound on `‖H₁‖` ALONE. -/

/-- **THE UNGAUGED HYPOTHESIS FORCES AN EXPLICIT SMALLNESS ON `‖H₁‖` AT THIS BACKGROUND.**
`72 = 2·36` is the counted factor: `36√2` is `rawErrorCoeff`'s own constant and `2` is §2's
deviation. -/
theorem hsmallFine_forces_H1_small {ell₀ : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (x₀ : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) (hell : 0 < ell)
    (hup : K * rawErrorCoeff ell (spikeU witnessMElem x₀) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3)) :
    K * (72 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
  have hα := two_le_frobSupBond_spikeU (L := L) x₀ μ hL
  have hcoef : (0 : ℝ) < 36 * Real.sqrt 2 / Real.sqrt (ell : ℝ) := by
    have hle : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    have : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr hle
    positivity
  have hre : rawErrorCoeff ell (spikeU witnessMElem x₀)
      = (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond (spikeU witnessMElem x₀) := rfl
  have hstep : K * (72 * Real.sqrt 2 / Real.sqrt (ell : ℝ))
      ≤ K * rawErrorCoeff ell (spikeU witnessMElem x₀) := by
    rw [hre]
    have hmul : (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * 2
        ≤ (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * frobSupBond (spikeU witnessMElem x₀) :=
      mul_le_mul_of_nonneg_left hα (le_of_lt hcoef)
    have hid : (72 * Real.sqrt 2 / Real.sqrt (ell : ℝ))
        = (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ)) * 2 := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hmul hK
  linarith

/-! ## §5 — NOTHING IS LOST: `γ = 1` IS THE UPSTREAM HYPOTHESIS VERBATIM -/

/-- At `γ = 1` the induced coarse gauge is the identity (definitionally) and the gauged fine
hypothesis IS `TerminalBinder.terminal_at_composed_carriers_generalFine`'s `hsmallFine`.  So §4a
contains the upstream statement and the witness above is a genuine ENLARGEMENT, not a swap. -/
theorem gauged_hypothesis_at_one (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (K r : ℝ) :
    coarseGauge h (fun _ => (1 : SU2)) = (fun _ => (1 : SU2)) ∧
      (K * rawErrorCoeff ell (periodicGaugeTransform (fun _ => (1 : SU2)) Ufine) ≤ r
        ↔ K * rawErrorCoeff ell Ufine ≤ r) := by
  refine ⟨rfl, ?_⟩
  rw [gaugeTransform_one]

/-! ## §6 — THE `ε` REGULATOR DOES NOT CONFLICT WITH COVARIANCE

The dispatch's third question.  `ε` enters `G₁⁻¹` as `ε·I`, and the gauge action is an ISOMETRY, so
the `ε`-summand is invariant on the nose: the coercivity modulus `1/ε` is the SAME number at every
point of the gauge orbit — it neither degrades nor has to be re-chosen. -/

/-- **THE `1/ε` COERCIVITY MODULUS IS A GAUGE INVARIANT.**  Both sides of the coercivity inequality
move together, so the constant is unchanged. -/
theorem eps_modulus_gauge_invariant (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (A : BondFnL2 L) :
    (‖gaugeL2 γ A‖ ^ 2 ≤ (1 / eps) * (inner ℝ (gaugeL2 γ A)
        (feedGinvGen h (periodicGaugeTransform γ Ufine) eps a (gaugeL2 γ A)) : ℝ))
      ↔ (‖A‖ ^ 2 ≤ (1 / eps) * (inner ℝ A (feedGinvGen h Ufine eps a A) : ℝ)) := by
  rw [norm_gaugeL2, feedGinvGen_quadForm_gauge]

/-- **AND THE `ε` SLOT ITSELF IS EXACTLY PRESERVED** — the three summands of the quadratic form are
individually invariant, so no part of the regulator is traded for covariance. -/
theorem feedGinv_summands_gauge_invariant (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (eps a : ℝ)
    (A : BondFnL2 L) :
    ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (periodicGaugeTransform γ Ufine)
        (gaugeL2 γ A)‖ ^ 2
      = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 Ufine A‖ ^ 2
    ∧ eps * ‖gaugeL2 γ A‖ ^ 2 = eps * ‖A‖ ^ 2
    ∧ a * ‖composedQ h (periodicGaugeTransform γ Ufine) (gaugeL2 γ A)‖ ^ 2
      = a * ‖composedQ h Ufine A‖ ^ 2 := by
  refine ⟨by rw [norm_curl_gaugeL2], by rw [norm_gaugeL2], by rw [norm_composedQ_gauge]⟩

/-! ## §7 — `Q` IS NOT INJECTIVE, AND `‖H₁‖` IS NOT SMALL FOR FREE

Two anti-vacuity anchors.  §7a is the dispatch's second trap (the carrier changed, so this is not
inherited); §7b makes §4's separation non-degenerate — `‖H₁‖` cannot be `0`. -/

/-- **`‖H₁‖` IS BOUNDED BELOW BY `1/‖Q‖`** at ANY datum with a nonzero coarse vector: the
interpolation identity `Q(H₁B) = B` alone forces it.  So the smallness §4 extracts from the
ungauged hypothesis is a real constraint, not one that `‖H₁‖ = 0` satisfies vacuously. -/
theorem one_le_normQ_mul_normH1 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (D : BalabanCovarianceData H K)
    (B : K) (hB : B ≠ 0) : 1 ≤ ‖D.Q‖ * ‖solutionOperator D‖ := by
  have hQB : D.Q (solutionOperator D B) = B := interpolates D B
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h1 : ‖B‖ ≤ ‖D.Q‖ * ‖solutionOperator D B‖ := by
    have hop : ‖D.Q (solutionOperator D B)‖ ≤ ‖D.Q‖ * ‖solutionOperator D B‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rwa [hQB] at hop
  have h2 : ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖B‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖B‖ ≤ ‖D.Q‖ * (‖solutionOperator D‖ * ‖B‖) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  nlinarith [h3, hBn]

end AdalyFormal.CovariantDatum
