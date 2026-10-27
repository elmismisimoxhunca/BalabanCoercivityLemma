/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawCarriers
import TerminalAssembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# THE FEED — `hraw` AT THE COMPOSED CARRIERS, CONSUMED BY `terminal_wired_posDef`

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.HrawCarriers

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM dstarDLM inner_dstarDLM_symm)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos gammaBrick_lower)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.TerminalAssembly (IsPrintedG1Form terminal_wired_posDef
  normSq_curlCLM_eq_dstarDCLM_form)
open AdalyFormal.HBaseInputs.CovData (build build_Q build_Ginv)

variable {L L' : PeriodicLatticeExtent}

/-! ## §A — THE DATUM ON THE COMPOSED CARRIERS

`Hs = BondFnL2 L` (the FINER torus), `Ks = BondFnL2 L'`, `Q = composedQ` — a genuinely
dimension-reducing block average followed by the extent identification, NOT the identity.  This is
the pair of carriers `compute/terminal_assembly/SCOPE.md` §7 residual 2 asks for.

`G₁⁻¹ := D_1^*D_1 + ε·I + a·Q^*Q` and `pen := √ε·I`, so (3.128) holds as an EQUALITY with
`d = ∂_1` and the SAME `a`.  The `ε·I` is what makes `G₁⁻¹` positive definite (the curl has a
kernel), and it is absorbed EXACTLY into the printed form's penalty slot `‖pen A‖²` — no term is
added to (3.128) and none is dropped. -/

/-- `G₁⁻¹` on the fine carrier. -/
noncomputable def feedGinv {ell : ℕ} (h : ScaleQuotient L ell L') (eps a : ℝ) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  dstarDCLM (trivialU L) + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
    + a • ((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
        (composedQ h (trivialU L)))

/-- The gauge-fixing/regularising penalty, `√ε·I`. -/
noncomputable def feedPen (eps : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (Real.sqrt eps) • (ContinuousLinearMap.id ℝ (BondFnL2 L))

theorem norm_feedPen_sq {eps : ℝ} (heps : 0 ≤ eps) (A : BondFnL2 L) :
    ‖(feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L) A‖ ^ 2 = eps * ‖A‖ ^ 2 := by
  show ‖(Real.sqrt eps) • A‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg eps), mul_pow,
    Real.sq_sqrt heps]

theorem inner_feedGinv {ell : ℕ} (h : ScaleQuotient L ell L') (eps a : ℝ) (A : BondFnL2 L) :
    (inner ℝ A (feedGinv h eps a A) : ℝ)
      = ‖curlCovariantCLM_L2 (trivialU L) A‖ ^ 2 + eps * ‖A‖ ^ 2
        + a * ‖composedQ h (trivialU L) A‖ ^ 2 := by
  show (inner ℝ A ((dstarDCLM (trivialU L) + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
    + a • ((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
      (composedQ h (trivialU L)))) A) : ℝ) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, inner_add_right, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, real_inner_smul_right,
    real_inner_smul_right]
  have hQ : (inner ℝ A (((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
      (composedQ h (trivialU L))) A) : ℝ) = ‖composedQ h (trivialU L) A‖ ^ 2 := by
    show (inner ℝ A (ContinuousLinearMap.adjoint (composedQ h (trivialU L))
      (composedQ h (trivialU L) A)) : ℝ) = _
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hQ, normSq_curlCLM_eq_dstarDCLM_form (trivialU L) A]
  show (inner ℝ A (dstarDCLM (trivialU L) A) : ℝ) + eps * (inner ℝ A A : ℝ) + _ = _
  rw [real_inner_self_eq_norm_sq]

theorem feedGinv_selfAdjoint {ell : ℕ} (h : ScaleQuotient L ell L') (eps a : ℝ)
    (x y : BondFnL2 L) :
    (inner ℝ (feedGinv h eps a x) y : ℝ) = inner ℝ x (feedGinv h eps a y) := by
  show (inner ℝ ((dstarDCLM (trivialU L) + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
      + a • ((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
        (composedQ h (trivialU L)))) x) y : ℝ)
    = inner ℝ x ((dstarDCLM (trivialU L) + eps • (ContinuousLinearMap.id ℝ (BondFnL2 L))
      + a • ((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
        (composedQ h (trivialU L)))) y)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
  have hd : (inner ℝ (dstarDCLM (trivialU L) x) y : ℝ) = inner ℝ x (dstarDCLM (trivialU L) y) := by
    show (inner ℝ (dstarDLM (trivialU L) x) y : ℝ) = inner ℝ x (dstarDLM (trivialU L) y)
    rw [inner_dstarDLM_symm]
  have hQ : (inner ℝ (((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
        (composedQ h (trivialU L))) x) y : ℝ)
      = inner ℝ x (((ContinuousLinearMap.adjoint (composedQ h (trivialU L))).comp
        (composedQ h (trivialU L))) y) := by
    show (inner ℝ (ContinuousLinearMap.adjoint (composedQ h (trivialU L))
        (composedQ h (trivialU L) x)) y : ℝ)
      = inner ℝ x (ContinuousLinearMap.adjoint (composedQ h (trivialU L))
        (composedQ h (trivialU L) y))
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  simp only [hd, hQ, ContinuousLinearMap.id_apply]

theorem feedGinv_posDef {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ} (heps : 0 < eps)
    (ha : 0 ≤ a) (x : BondFnL2 L) (hx : x ≠ 0) : (0 : ℝ) < inner ℝ x (feedGinv h eps a x) := by
  rw [inner_feedGinv]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : (0 : ℝ) ≤ ‖curlCovariantCLM_L2 (trivialU L) x‖ ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ a * ‖composedQ h (trivialU L) x‖ ^ 2 :=
    mul_nonneg ha (sq_nonneg _)
  nlinarith [mul_pos heps (pow_pos hn 2)]

/-- **THE DATUM.**  Built with `CovDataCtor.build` (REUSED), whose `Q`-surjectivity input is
§7e's `composedQ_surjective`. -/
noncomputable def feedDatum {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ} (heps : 0 < eps)
    (ha : 0 ≤ a) : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L') :=
  build (feedGinv h eps a) (composedQ h (trivialU L)) (feedGinv_selfAdjoint h eps a)
    (feedGinv_posDef h heps ha) (composedQ_surjective h)

theorem feedDatum_Q {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ} (heps : 0 < eps)
    (ha : 0 ≤ a) : (feedDatum h heps ha).Q = composedQ h (trivialU L) := rfl

theorem feedDatum_Ginv {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ} (heps : 0 < eps)
    (ha : 0 ≤ a) : (feedDatum h heps ha).Ginv = feedGinv h eps a := rfl

/-- **(3.128) HOLDS AT THE DATUM, AS AN EQUALITY**, with `d = ∂_1`, `pen = √ε·I` and the same `a`. -/
theorem feedDatum_isPrintedG1Form {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ}
    (heps : 0 < eps) (ha : 0 ≤ a) :
    IsPrintedG1Form (feedDatum h heps ha) a (curlCovariantCLM_L2 (trivialU L))
      (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L) := by
  intro A
  rw [feedDatum_Ginv h heps ha, inner_feedGinv, norm_feedPen_sq (le_of_lt heps) A]
  rw [feedDatum_Q h heps ha]

/-- **`hraw` HOLDS AT THE DATUM, AT EVERY BACKGROUND `U` ON `L'`**, with
`σ₀ = ℓ^{-1/2}` and `κ = 4√2·α₁(U)`.  This is §7c read at the datum — the ONE analytic input of
`terminal_wired_posDef`, at carriers where `Q` is not the identity. -/
theorem feedDatum_hraw {ell : ℕ} (h : ScaleQuotient L ell L') {eps a : ℝ} (heps : 0 < eps)
    (ha : 0 ≤ a) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U ((feedDatum h heps ha).Q A)‖
      ≤ AdalyFormal.MechEdges.G16.rawSigmaZero ell
          * ‖curlCovariantCLM_L2 (trivialU L) A‖
        + 4 * Real.sqrt 2 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
          * ‖(feedDatum h heps ha).Q A‖ := by
  rw [feedDatum_Q h heps ha]
  exact hraw_composed_flatFine h U A

/-! ## §B — THE DRIFT COEFFICIENT AGAINST THE HALF-DRIFT HYPOTHESIS

`terminal_wired_posDef` needs `κ ≤ ½√(gammaBrick ell₀)`.  §A delivers `κ = 4√2·α₁(U)`.  §B computes,
in exact rationals, the smallness on `α₁(U)` that makes the two meet.  Every factor is counted:
`√345960 ≤ 589` (`589² = 346921 ≥ 345960`), `√2 ≤ 1.4143` (`1.4143² = 2.00024449 ≥ 2`), and
`4·1.4143·2·589 = 6664.1816 ≤ 6668`. -/

theorem sqrt_two_le : Real.sqrt 2 ≤ 1.4143 := by
  rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt_gammaBrick_lower {ell₀ : ℕ} (hell : 0 < ell₀) :
    1 / (589 * (ell₀ : ℝ) ^ 3) ≤ Real.sqrt (gammaBrick ell₀) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hlow := gammaBrick_lower hell
  have hy : (0 : ℝ) ≤ 1 / (589 * (ell₀ : ℝ) ^ 3) := by positivity
  rw [show (1 : ℝ) / (589 * (ell₀ : ℝ) ^ 3) = Real.sqrt ((1 / (589 * (ell₀ : ℝ) ^ 3)) ^ 2) from
    (Real.sqrt_sq hy).symm]
  refine Real.sqrt_le_sqrt ?_
  refine le_trans ?_ hlow
  rw [div_pow, one_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : ((ell₀ : ℝ) ^ 3) ^ 2 = (ell₀ : ℝ) ^ 6 := by ring
  rw [hp]
  nlinarith [pow_pos h0 6]

/-- **THE SMALLNESS THAT MAKES `κ = 4√2·α₁` MEET `κ ≤ ½√(gammaBrick ell₀)`.**  Constant `6668`,
derived (not fitted) from `589` and `1.4143` above. -/
theorem halfDrift_of_alpha_small {ell₀ : ℕ} (hell : 0 < ell₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hα : AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
      ≤ 1 / (6668 * (ell₀ : ℝ) ^ 3)) :
    4 * Real.sqrt 2 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
      ≤ Real.sqrt (gammaBrick ell₀) / 2 := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  have hα0 := AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hs := sqrt_two_le
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hg := sqrt_gammaBrick_lower hell
  -- `4√2·α₁ ≤ 4·1.4143·α₁ ≤ 4·1.4143/(6668·ell³) ≤ 1/(1178·ell³) ≤ ½√γ`
  have hstep1 : 4 * Real.sqrt 2 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
      ≤ 4 * 1.4143 * (1 / (6668 * (ell₀ : ℝ) ^ 3)) := by
    have hA : 4 * Real.sqrt 2 ≤ 4 * 1.4143 := by linarith
    have hB : (0 : ℝ) ≤ 4 * Real.sqrt 2 := by positivity
    nlinarith [hα, hα0, hA, hB]
  have hstep2 : 4 * 1.4143 * (1 / (6668 * (ell₀ : ℝ) ^ 3))
      ≤ 1 / (589 * (ell₀ : ℝ) ^ 3) / 2 := by
    have hL : 4 * 1.4143 * (1 / (6668 * (ell₀ : ℝ) ^ 3))
        = (4 * 1.4143) / (6668 * (ell₀ : ℝ) ^ 3) := by ring
    have hR : 1 / (589 * (ell₀ : ℝ) ^ 3) / 2 = 1 / (1178 * (ell₀ : ℝ) ^ 3) := by
      rw [div_div]
      congr 1
      ring
    rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp3]
  linarith

/-- **§D1 — THE COMPOSED ROUTE NEEDS A STRICTLY TIGHTER SMALLNESS THAN THE PRINTED (3.35) CLASS.**
`1/(6668·ell₀³) < 1/(186·ell₀³)` for every `ell₀ ≥ 1`: the smallness §C consumes is stronger than
`hthr`, so `hsmall` is NOT implied by the printed class and is a genuine extra hypothesis. -/
theorem sixSixSixEight_strictly_smaller {ell₀ : ℕ} (hell : 0 < ell₀) :
    1 / (6668 * (ell₀ : ℝ) ^ 3) < 1 / (186 * (ell₀ : ℝ) ^ 3) := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp : (0 : ℝ) < (ell₀ : ℝ) ^ 3 := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hp]

/-! ## §C — THE FEED: `terminal_wired_posDef` APPLIED, WITH `hraw` FILLED BY A THEOREM -/

/-- **THE TERMINAL STATEMENT AT THE COMPOSED CARRIERS.**

Every COVARIANCE-side hypothesis of `TerminalAssembly.terminal_wired_posDef` is discharged here:
`hform` by `feedDatum_isPrintedG1Form`, `hraw` by `feedDatum_hraw` (i.e. by
`MechG16.hraw_op` transported across the extent identification and drift-corrected on the coarse
side), `hσ₀`/`hκ` by arithmetic, and `hhalf` by §B from the single smallness
`α₁(U) ≤ 1/(6668·ell₀³)`.  The SOURCE-side hypotheses are carried unchanged, exactly as
`terminal_wired_posDef` states them.

**`Q` here is the block average followed by the extent identification** — the carriers are
`BondFnL2 L → BondFnL2 L'` with `L` the FINER torus, not `Hs = Ks` with `Q = I`. -/
theorem terminal_at_composed_carriers {ell ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (hell2 : 2 ≤ ell₀) (hstrict : ∀ ν : Fin 3, ell₀ < L' ν + 1)
    (hdvd0 : ∀ ν : Fin 3, ell₀ ∣ (L' ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (hsmall : AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
      ≤ 1 / (6668 * (ell₀ : ℝ) ^ 3))
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (Qext : BondFnL2 L' → BondFnL2 L') (T : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (S : BondFnL2 L' →L[ℝ] BondFnL2 L')
    (hS : IsSourceOperator (feedDatum h heps (le_of_lt bc.a_pos)) Qext (T (JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 L', ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatum h heps (le_of_lt bc.a_pos))‖) (hT : 0 < ‖T‖)
    (hcard : 0 < Fintype.card (Bond L'))
    (hδ : δ < 1 / (1370001600 * (ell₀ : ℝ) ^ 6
      * (AdalyFormal.MechEdges.G16.rawSigmaZero ell) ^ 2
      * ‖solutionOperator (feedDatum h heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond L'))))))
    (w : TildeFn L' ell₀) (hw : w ≠ 0) :
    0 < cdcFormTrue (feedDatum h heps (le_of_lt bc.a_pos)) bc Qext (T (JsuTwo U)) U ell₀
      (dinvC U ell₀) w := by
  have hell : 0 < ell₀ := by omega
  -- `hthr` is NOT a separate hypothesis: §4c's smallness is strictly stronger
  -- (`sixSixSixEight_strictly_smaller`), so the printed class membership is DERIVED here rather
  -- than assumed alongside.  Carrying both would have been a redundant binder.
  have hthr : AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
      ≤ 1 / (186 * (ell₀ : ℝ) ^ 3) :=
    le_trans hsmall (le_of_lt (sixSixSixEight_strictly_smaller hell))
  refine terminal_wired_posDef hell2 hstrict hdvd0 U hthr
    (feedDatum h heps (le_of_lt bc.a_pos)) bc (curlCovariantCLM_L2 (trivialU L))
    (feedPen eps : BondFnL2 L →L[ℝ] BondFnL2 L)
    (feedDatum_isPrintedG1Form h heps (le_of_lt bc.a_pos))
    (AdalyFormal.MechEdges.G16.rawSigmaZero ell)
    (4 * Real.sqrt 2 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U)
    (AdalyFormal.MechEdges.G16.rawSigmaZero_pos (ell_pos_of_scale h))
    (mul_nonneg (by positivity)
      (AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U))
    (halfDrift_of_alpha_small hell U hsmall)
    (feedDatum_hraw h heps (le_of_lt bc.a_pos) U)
    Qext T S hS c₂ hc₂ hD2 δ hδ0 hU hH1 hT hcard hδ w hw

/-! ## §C2 — THE TERMINAL SHAPE AT A **GENERAL** FINE BACKGROUND, ON THE MINIMISER RANGE

§7d named the sufficient condition `‖A‖ ≤ ρ‖QA‖`.  On the range of the solution operator `H₁` it
HOLDS, with `ρ = ‖H₁‖`, from the interpolation identity `Q(H₁B) = B` alone — and that range is
exactly the set of vectors `StokesCommu.Restricted.perturbed_chain_at_minimizer` evaluates.

**What this does NOT do:** `terminal_wired_posDef`'s binder is `∀ A : Hs`, not `∀ B, at H₁B`, so
this does not discharge that binder at a general fine background.  It is stated because it is the
exact reach of the method, not because it closes the gap. -/

theorem hraw_composed_at_minimizer {ell : ℕ} (h : ScaleQuotient L ell L')
    (D : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L'))
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hQ : D.Q = composedQ h Ufine)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (B : BondFnL2 L') :
    ‖curlCovariantCLM_L2 U (D.Q (solutionOperator D B))‖
      ≤ AdalyFormal.MechEdges.G16.rawSigmaZero ell
          * ‖curlCovariantCLM_L2 Ufine (solutionOperator D B)‖
        + (4 * Real.sqrt 2 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U
            + ‖solutionOperator D‖ * AdalyFormal.MechEdges.G16.rawErrorCoeff ell Ufine)
          * ‖D.Q (solutionOperator D B)‖ := by
  have hQB : D.Q (solutionOperator D B) = B :=
    AdalyFormal.Balaban.VariationalProjectorH1.interpolates D B
  have hnorm : ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖B‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [hQ] at hQB
  rw [hQ]
  rw [hQB]
  have hg := hraw_composed_general h Ufine U (solutionOperator D B)
  rw [hQB] at hg
  have hce : (0 : ℝ) ≤ AdalyFormal.MechEdges.G16.rawErrorCoeff ell Ufine :=
    AdalyFormal.MechEdges.G16.rawErrorCoeff_nonneg ell Ufine
  nlinarith [hg, hnorm, hce]

/-! ## §D — WHAT STILL SEPARATES THIS FROM THE PRINTED CLASS HYPOTHESIS ALONE

Two facts, both exact rationals, both stated as theorems rather than as prose. -/

/-- **§D2 — AND THE GAP IS A PURE CONSTANT: THE `ell₀`-SCALING IS UNCHANGED.**  The ratio of the two
thresholds is exactly `6668/186 = 1667/46.5`, independent of `ell₀` — i.e. the composed route does
not cost a power of `ell₀`, only the factor below. -/
theorem threshold_ratio_is_ell_free {ell₀ : ℕ} (hell : 0 < ell₀) :
    (1 / (186 * (ell₀ : ℝ) ^ 3)) / (1 / (6668 * (ell₀ : ℝ) ^ 3)) = 6668 / 186 := by
  have h1 : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell
  have h0 : (0 : ℝ) < (ell₀ : ℝ) := by linarith
  have hp : ((ell₀ : ℝ) ^ 3) ≠ 0 := by positivity
  field_simp

/-! ### §D3 — THE TIGHTENED CLASS IS **NOT** EMPTY OF CURVED BACKGROUNDS

The obvious objection to §4c's `1/(6668·ell₀³)` is that it might admit only `U = 1`.  It does not:
`CovLemma24Witness.witU` is a one-parameter rotation family with `α₁(witU t) = √(8t²/(1+t²))`
EXACTLY (that lane's own theorem, CITED), so a smaller parameter lands inside.  The lane's own
`witT = 10⁻⁵` gives `α₁ ≈ 2.83·10⁻⁵`, which meets `1/(186·3³) = 1.99·10⁻⁴` but NOT
`1/(6668·3³) = 5.55·10⁻⁶`; `tightT = 10⁻⁶` gives `α₁ ≈ 2.83·10⁻⁶` and meets both. -/

/-- A rotation parameter small enough for §4c's class at `ell₀ = 3`. -/
noncomputable def tightT : ℝ := 1 / 1000000

theorem tightT_alpha_pos :
    0 < AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
      (AdalyFormal.Balaban.CovLemma24Witness.witU tightT) := by
  rw [AdalyFormal.Balaban.CovLemma24Witness.frobSupBond_witU]
  refine Real.sqrt_pos.mpr ?_
  rw [tightT]
  norm_num

theorem tightT_alpha_le :
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
      ≤ 1 / (6668 * ((3 : ℕ) : ℝ) ^ 3) := by
  rw [AdalyFormal.Balaban.CovLemma24Witness.frobSupBond_witU]
  have hle : 8 * tightT ^ 2 / (1 + tightT ^ 2) ≤ (1 / (6668 * ((3 : ℕ) : ℝ) ^ 3)) ^ 2 := by
    rw [tightT]
    norm_num
  refine (Real.sqrt_le_sqrt hle).trans (le_of_eq ?_)
  exact Real.sqrt_sq (by norm_num)

theorem tightT_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
        (AdalyFormal.Balaban.CovLemma24Witness.witBond.1,
         AdalyFormal.Balaban.CovLemma24Witness.witDir)
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [AdalyFormal.Balaban.RegularUCurvedWitness.holonomy_singleBond_base_plaquette
    (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
    AdalyFormal.Balaban.CovLemma24Witness.witBond.1
    AdalyFormal.Balaban.CovLemma24Witness.witDir
    (AdalyFormal.Balaban.NonFlatBackground.rotElem tightT)
    (AdalyFormal.Balaban.RegularUCurvedWitness.bondU_at
      AdalyFormal.Balaban.CovLemma24Witness.witBond _)
    (fun _ hb => AdalyFormal.Balaban.RegularUCurvedWitness.bondU_off
      AdalyFormal.Balaban.CovLemma24Witness.witBond _ hb) (by decide)]
  refine AdalyFormal.Balaban.NonFlatBackground.rotElem_ne_one ?_
  rw [tightT]
  norm_num

/-- **THE TIGHTENED CLASS IS INHABITED AT A CURVED BACKGROUND** — plaquette holonomy `≠ 1`,
`α₁ > 0`, and `α₁ ≤ 1/(6668·3³)`, so §4c's smallness is not a statement about `U = 1` in disguise.
It also meets the printed `1/(186·3³)`, so it is admissible for `hthr` as well. -/
theorem tightened_class_curved_inhabited :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
        (AdalyFormal.Balaban.CovLemma24Witness.witBond.1,
         AdalyFormal.Balaban.CovLemma24Witness.witDir)
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    ∧ 0 < AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
    ∧ AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
        ≤ 1 / (6668 * ((3 : ℕ) : ℝ) ^ 3)
    ∧ AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
        (AdalyFormal.Balaban.CovLemma24Witness.witU tightT)
        ≤ 1 / (186 * ((3 : ℕ) : ℝ) ^ 3) :=
  ⟨tightT_curved, tightT_alpha_pos, tightT_alpha_le,
    le_trans tightT_alpha_le (le_of_lt (sixSixSixEight_strictly_smaller (by norm_num)))⟩

#print axioms feedGinv
#print axioms feedPen
#print axioms norm_feedPen_sq
#print axioms inner_feedGinv
#print axioms feedGinv_selfAdjoint
#print axioms feedGinv_posDef
#print axioms feedDatum
#print axioms feedDatum_Q
#print axioms feedDatum_Ginv
#print axioms feedDatum_isPrintedG1Form
#print axioms feedDatum_hraw
#print axioms sqrt_two_le
#print axioms sqrt_gammaBrick_lower
#print axioms halfDrift_of_alpha_small
#print axioms sixSixSixEight_strictly_smaller
#print axioms terminal_at_composed_carriers
#print axioms hraw_composed_at_minimizer
#print axioms threshold_ratio_is_ell_free
#print axioms tightT
#print axioms tightT_alpha_pos
#print axioms tightT_alpha_le
#print axioms tightT_curved
#print axioms tightened_class_curved_inhabited

end AdalyFormal.HrawCarriers
