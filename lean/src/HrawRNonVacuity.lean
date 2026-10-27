/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawRDischarge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `HrawRNonVacuity.lean` — THE HYPOTHESIS SET OF `terminal_sum_at_star_datum` IS INHABITED

Lane `compute/hrawr_discharge/`.  Write scope: that directory only.  Never `lake build`.

`HrawRDischarge` §6 removes five binders from the recomposed headline.  A theorem with fewer
binders is worth nothing if the remaining ones cannot be met, so this file discharges every binder
of §6 **except the two [SOURCE] ones** — `hprinted` (CMP99b (3.35)) and `hgeom` — which are
retained deliberately: they are exactly the inputs the recomposition exists to consume, and
`RecomposeSum.terminal_sum_posDef_from_printed` carries them too.

## WHAT THE ROW IS AND IS NOT (read before quoting it)

* The background is `U ≡ −1` (`centerU witnessL`).  It is **not** the flat one, it is **not** in
  the global smallness class (`α₁ = 2√2`, the largest value the quantity takes), and `κ = 0` there
  by `HrawRDischarge` §5 — so the row exercises exactly the centre-blindness that file establishes.
* The source `J = Q*v` is **nonzero** and its source term at `C₀B̃` is **strictly positive**
  (`DatumWitness.sourceTerm_Qstar_pos`), so this is not the vanishing-source degeneracy
  `TerminalAssembly.end_to_end_flat` discloses.  It is `v` that is small, not `J` that is absent.
* `v` is a FREE vector of the coarse carrier, **not** `JsuTwo(U)`.  The recomposed headline's `J`
  slot is free (it is tied to a background only in `terminal_wired_posDef`), so this is legitimate
  — but it means the row establishes SATISFIABILITY of §6's hypothesis set and not the faithful
  source wiring.  That distinction is the one `datum_witness/SCOPE.md` draws for its own §4.

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.HrawRDischarge

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.AlphaAnalyticity (centerU)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.DeltaKWiring (bondQext cdcFormTrue sourceTerm norm_cZero_pos)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst assemblyDatum_hD2)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.RecomposeSum (gammaSum gammaSum_lower CubesRefine)
open AdalyFormal.MechEdges.G16 (rawSigmaZero)
open AdalyFormal.DatumWitness (fineL starScale starDatum starDatum_Q isSourceOperator_Qstar
  sourceTerm_Qstar_pos Qstar_source_ne_zero rawSigmaZero_two_sq)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale dvd_of_scale coarseFnL2Equiv
  composedQ composedQ_apply)
open AdalyFormal.Balaban.BridgeInverse (qCLM)
open AdalyFormal.HoleHunt.CenterBlindness (centralFlipConfig)

/-! ## §7 — `‖Q*‖ ≤ ‖Q‖`, AND BOTH ARE `≤ 1` AT THE STAR DATUM

`BalabanCovarianceData` carries `Qstar` as a SEPARATE field with only the adjoint identity
`⟨Qx,y⟩ = ⟨x,Q*y⟩`, so `‖Q*‖ = ‖Q‖` is not available from mathlib's `adjoint`.  §7a derives the
inequality that is needed from that identity alone, at EVERY datum. -/

/-- **`‖Q*y‖ ≤ ‖Q‖·‖y‖` FROM THE ADJOINT IDENTITY ALONE.**  `‖Q*y‖² = ⟨Q(Q*y), y⟩`. -/
theorem norm_Qstar_apply_le {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (D : BalabanCovarianceData H K) (y : K) :
    ‖D.Qstar y‖ ≤ ‖D.Q‖ * ‖y‖ := by
  have hid : (inner ℝ (D.Q (D.Qstar y)) y : ℝ) = inner ℝ (D.Qstar y) (D.Qstar y) :=
    D.Q_Qstar_adjoint (D.Qstar y) y
  have hself : (inner ℝ (D.Qstar y) (D.Qstar y) : ℝ) = ‖D.Qstar y‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hcs : (inner ℝ (D.Q (D.Qstar y)) y : ℝ) ≤ ‖D.Q (D.Qstar y)‖ * ‖y‖ :=
    real_inner_le_norm _ _
  have hop : ‖D.Q (D.Qstar y)‖ ≤ ‖D.Q‖ * ‖D.Qstar y‖ := D.Q.le_opNorm _
  have hsq : ‖D.Qstar y‖ ^ 2 ≤ (‖D.Q‖ * ‖y‖) * ‖D.Qstar y‖ := by
    rw [← hself, ← hid]
    calc (inner ℝ (D.Q (D.Qstar y)) y : ℝ) ≤ ‖D.Q (D.Qstar y)‖ * ‖y‖ := hcs
      _ ≤ (‖D.Q‖ * ‖D.Qstar y‖) * ‖y‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = (‖D.Q‖ * ‖y‖) * ‖D.Qstar y‖ := by ring
  rcases (norm_nonneg (D.Qstar y)).lt_or_eq with hpos | hzero
  · nlinarith [hsq, hpos]
  · rw [← hzero]
    positivity

/-- **`‖composedQ‖ ≤ 1` FOR `ℓ ≥ 2`.**  `‖composedQ‖ = ‖qCLM‖` (the extent identification is an
isometry) and `‖qCLM‖ ≤ √(ℓ⁻³) < 1` (`QCLMNorm.qCLM_opNorm_lt_one`, REUSED). -/
theorem opNorm_composedQ_le_one {L L' : PeriodicLatticeExtent} {ell : ℕ}
    (h : ScaleQuotient L ell L') (hell2 : 2 ≤ ell)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖composedQ h Ufine‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun A => ?_)
  have hval : ‖composedQ h Ufine A‖ = ‖qCLM Ufine ell A‖ := by
    rw [composedQ_apply]
    exact (coarseFnL2Equiv h).norm_map _
  have hq : ‖qCLM Ufine ell A‖ ≤ ‖qCLM Ufine ell‖ * ‖A‖ := (qCLM Ufine ell).le_opNorm A
  have hlt : ‖qCLM Ufine ell‖ < 1 :=
    AdalyFormal.Balaban.QCLMNorm.qCLM_opNorm_lt_one hell2 (dvd_of_scale h) Ufine
  rw [hval]
  nlinarith [hq, hlt, norm_nonneg A]

/-- **AT `D*`: `‖Q*y‖ ≤ ‖y‖`.** -/
theorem starDatum_norm_Qstar_apply_le (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (y : BondFnL2 witnessL) :
    ‖(starDatum bc heps).Qstar y‖ ≤ ‖y‖ := by
  have h1 := norm_Qstar_apply_le (starDatum bc heps) y
  have h2 : ‖(starDatum bc heps).Q‖ ≤ 1 := by
    rw [starDatum_Q bc heps]
    exact opNorm_composedQ_le_one starScale (by norm_num) (trivialU fineL)
  nlinarith [h1, h2, norm_nonneg y, norm_nonneg ((starDatum bc heps).Qstar y)]

/-! ## §8 — THE FLOOR CONSTANT AT `κ = 0`, AS AN EXPLICIT RATIONAL

`sharpFloorConst γ 0 σ₀ = γ/σ₀²`, and `σ₀² = ½` at `ℓ = 2` (`DatumWitness.rawSigmaZero_two_sq`,
REUSED), so the constant is `2·gammaSum 2 ≥ 2/88565760 = 1/44282880`.
`88565760 = 1383840·64` is `RecompFloor.gammaSum_lower` at `ℓ = 2`. -/

theorem sharpFloorConst_star_lower :
    1 / 44282880 ≤ sharpFloorConst (gammaSum 2) 0 (rawSigmaZero 2) := by
  have hlow := gammaSum_lower (by norm_num : 0 < 2)
  have hnum : (1 : ℝ) / (1383840 * (((2 : ℕ)) : ℝ) ^ 6) = 1 / 88565760 := by norm_num
  rw [hnum] at hlow
  have hγ0 : (0 : ℝ) ≤ gammaSum 2 := by linarith
  have hσ : rawSigmaZero 2 ^ 2 = 1 / 2 := rawSigmaZero_two_sq
  have hval : sharpFloorConst (gammaSum 2) 0 (rawSigmaZero 2) = 2 * gammaSum 2 := by
    show ((Real.sqrt (gammaSum 2) - 0) / rawSigmaZero 2) ^ 2 = 2 * gammaSum 2
    rw [sub_zero, div_pow, hσ, Real.sq_sqrt hγ0]
    ring
  rw [hval]
  linarith

/-! ## §9 — EVERY REMAINING BINDER OF §6, DISCHARGED

`ε = fun _ => true`, `V = 1`, so the background is `centerU witnessL` and the drift price is `0`.
The source is `J = Q*v` with `v` a nonzero vector of the coarse carrier of norm at most `1/40000`;
`18·(1/40000)² = 9/800000000 = 1.125·10⁻⁸ < 2.258·10⁻⁸ = 1/44282880`, which is the whole of the threshold
arithmetic and is exhibited rather than asserted. -/

/-- **THE ROW.**  Only `hprinted` and `hgeom` (both [SOURCE]) remain. -/
theorem star_recomposed_inhabited
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (hbig : 1024 + bc.a ≤ eps)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj (centerU witnessL) 𝒞src)
    (hgeom : CubesRefine AdalyFormal.Balaban.CurvedContent.witnessL_dvd
      (Finset.univ : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))
      (fun z => ({z} : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))) 𝒞src)
    (v : BondFnL2 witnessL) (hvsmall : ‖v‖ ≤ 1 / 40000)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc (bondQext v) ((starDatum bc heps).Qstar v)
      (centerU witnessL) 2 (dinvC (centerU witnessL) 2) w := by
  have hH1 : ‖solutionOperator (starDatum bc heps)‖ ≤ 9 :=
    starDatum_norm_H1_le_nine bc heps hbig
  have hQs : ‖(starDatum bc heps).Qstar v‖ ≤ ‖v‖ := starDatum_norm_Qstar_apply_le bc heps v
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hH10 : (0 : ℝ) ≤ ‖solutionOperator (starDatum bc heps)‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  -- the threshold, in exact rationals
  have hRthr : 2 * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖
        * ‖(starDatum bc heps).Qstar v‖
      < sharpFloorConst (gammaSum 2) (4 * Real.sqrt 2 * frobSupBond (trivialU witnessL))
          (rawSigmaZero 2) := by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU witnessL, mul_zero]
    have hlow := sharpFloorConst_star_lower
    have ha : 2 * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖
          * ‖(starDatum bc heps).Qstar v‖
        ≤ 2 * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_left hQs (by positivity)
    have hnn : (0 : ℝ) ≤ ‖v‖ * ‖v‖ := mul_nonneg hv0 hv0
    have hb : 2 * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖ * ‖v‖
        ≤ 2 * 9 * ‖v‖ * ‖v‖ := by
      have hcoef : 2 * ‖solutionOperator (starDatum bc heps)‖ ≤ 2 * 9 := by linarith
      calc 2 * ‖solutionOperator (starDatum bc heps)‖ * ‖v‖ * ‖v‖
          = (2 * ‖solutionOperator (starDatum bc heps)‖) * (‖v‖ * ‖v‖) := by ring
        _ ≤ (2 * 9) * (‖v‖ * ‖v‖) := mul_le_mul_of_nonneg_right hcoef hnn
        _ = 2 * 9 * ‖v‖ * ‖v‖ := by ring
    have hc2 : (2 : ℝ) * 9 * ‖v‖ * ‖v‖ ≤ 9 / 800000000 := by
      have hmm : ‖v‖ * ‖v‖ ≤ (1 / 40000) * (1 / 40000) :=
        mul_le_mul hvsmall hvsmall hv0 (by norm_num)
      nlinarith [hmm]
    have hnum : (9 : ℝ) / 800000000 < 1 / 44282880 := by norm_num
    linarith
  have hcenter : centerU witnessL = centralFlipConfig (fun _ => true) (trivialU witnessL) :=
    centerU_eq_flip
  have hdrift : frobSupBond (trivialU witnessL) ≤ 1 / (13336 * (((2 : ℕ)) : ℝ) ^ 3) := by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU witnessL]
    positivity
  rw [hcenter]
  exact terminal_sum_at_star_datum bc heps (fun _ => true) (trivialU witnessL) hdrift c M α₀ η Lj
    hη hηne hLj hc hM hα0 hthr 𝒞src (by rw [← hcenter]; exact hprinted) hgeom
    (bondQext v) ((starDatum bc heps).Qstar v)
    ((‖v‖ ^ 2 : ℝ) • (1 : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL))
    (isSourceOperator_Qstar (starDatum bc heps) v) ‖v‖ hv0
    (assemblyDatum_hD2 v) ‖(starDatum bc heps).Qstar v‖ le_rfl hRthr w hw

/-- **AND THE ROW IS NOT THE VANISHING-SOURCE DEGENERACY.**  At any `v ≠ 0` the source vector is
nonzero and its source term at `C₀B̃` is STRICTLY positive — so `−2·sourceTerm` genuinely opposes the
floor in the instance §9 exhibits.  Both facts are `DatumWitness`'s, REUSED. -/
theorem star_recomposed_source_present (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (v : BondFnL2 witnessL) (hv : v ≠ 0) (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    (starDatum bc heps).Qstar v ≠ 0
    ∧ 0 < sourceTerm (starDatum bc heps) (bondQext v) ((starDatum bc heps).Qstar v)
        (cZero (centerU witnessL) 2 (dinvC (centerU witnessL) 2) w) :=
  ⟨Qstar_source_ne_zero (starDatum bc heps) v hv,
    sourceTerm_Qstar_pos (starDatum bc heps) v _ hv
      (norm_pos_iff.mp (norm_cZero_pos (centerU witnessL) (dinvC (centerU witnessL) 2) w hw))⟩

/-- **AND THE `v` WINDOW IS INHABITED BY A NONZERO VECTOR** — so §9's two rows can be read
together.  Any nonzero `v₀` rescaled to norm `1/40000` does it. -/
theorem v_window_inhabited (v₀ : BondFnL2 witnessL) (hv₀ : v₀ ≠ 0) :
    ∃ v : BondFnL2 witnessL, v ≠ 0 ∧ ‖v‖ ≤ 1 / 40000 := by
  have hn : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  refine ⟨(1 / (40000 * ‖v₀‖)) • v₀, ?_, ?_⟩
  · refine smul_ne_zero ?_ hv₀
    positivity
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (40000 * ‖v₀‖))]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    ring_nf
    linarith

#print axioms norm_Qstar_apply_le
#print axioms opNorm_composedQ_le_one
#print axioms starDatum_norm_Qstar_apply_le
#print axioms sharpFloorConst_star_lower
#print axioms star_recomposed_inhabited
#print axioms star_recomposed_source_present
#print axioms v_window_inhabited

end AdalyFormal.HrawRDischarge
