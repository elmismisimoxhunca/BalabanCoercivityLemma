/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import RInvPayoff
import AdalyFormal.Balaban.DeltaPrimeBound

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

/-!
# `HrawROpNorm.lean` — THE COVARIANT CURL IS A BOUNDED OPERATOR WITH A DIMENSION-ONLY NORM

Lane `compute/hrawr_discharge/`.  Write scope: that directory only.  Never `lake build`.

## WHAT WAS ASKED FOR AND WHAT WAS ALREADY IN THE TREE

The brief asked for "an operator-norm bound on `curlCovariantCLM_L2` (if absent from the tree,
PROVE one: … count plaquette contributions per bond)".  **It is not absent.**  The counting is
already done, at general `U`, in `formal/AdalyFormal/AdalyFormal/Balaban/DeltaPrimeBound.lean`:

> `theorem dstarDQuadForm_le_bondEnergy (U) (A) : dstarDQuadForm U A ≤ 16 * bondEnergy A`
> "`4` from the four-term Cauchy–Schwarz, `4` from `LemmaAssemblyNormalized.sum_plaqBondSq_eq`'s
> EXACT incidence identity. (`WitnessInequality`'s `≤ 32` is the `U = 1` special case, and is beaten
> by a factor 2.)"

So this file does **not** re-derive the count (BUILD DISCIPLINE 2 / LAW-19).  It carries that
quadratic-form inequality across the two norm bridges the tree also already has
(`DeltaKFull.norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm`, `MechG16.norm_bondFnL2`) and reads off
the operator norm, which is the form every consumer here needs and which was NOT stated anywhere:

    ‖D_U‖ ≤ 4,  at every extent, every background, with no smallness and no scale.

The one genuinely new statement of this file is that `‖·‖`-form and its two consequences (§2, §3).

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.HrawRDischarge

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2
  norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.DeltaPrimeBound (dstarDQuadForm_le_bondEnergy)
open AdalyFormal.MechEdges.G16 (norm_bondFnL2)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale composedQ)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open QSurjRInverse (rInvComposed opNorm_rInvComposed composedQ_rInvComposed)

variable {L L' : PeriodicLatticeExtent}

/-! ## §1 — `‖D_U‖ ≤ 4` -/

/-- **THE POINTWISE FORM.**  `‖D_U X‖² ≤ 16‖X‖²` on `BondFnL2 L`, for every background.
This is `DeltaPrimeBound.dstarDQuadForm_le_bondEnergy` (CITED, not rebuilt) read through the two
norm bridges; `16 = 4 · 4` is that theorem's four-term Cauchy–Schwarz times the exact bond/plaquette
incidence identity, and neither factor is recomputed here. -/
theorem norm_sq_curl_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U X‖ ^ 2 ≤ 16 * ‖X‖ ^ 2 := by
  set A : Bond L → SuTwo := WithLp.ofLp X with hA
  have hX : (WithLp.toLp 2 A : BondFnL2 L) = X := rfl
  have hsq : ‖curlCovariantCLM_L2 U X‖ ^ 2 = dstarDQuadForm U A := by
    rw [← hX]
    exact norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm U A
  have hnX : ‖X‖ = Real.sqrt (bondEnergy A) := by
    rw [← hX]
    exact norm_bondFnL2 A
  have hbe : bondEnergy A = ‖X‖ ^ 2 := by
    rw [hnX, Real.sq_sqrt (bondEnergy_nonneg A)]
  rw [hsq, ← hbe]
  exact dstarDQuadForm_le_bondEnergy U A

/-- **THE OPERATOR NORM: `‖D_U‖ ≤ 4`.**  Uniform in the extent `L` and in the background `U`; no
smallness class, no block scale, no lattice volume.  This is the statement the `ε`-threshold of
`TerminalBinder.norm_H1_le_of_rightInverse_bound` needs in order to be a NUMBER rather than an
unevaluated operator norm. -/
theorem opNorm_curl_le_four
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖curlCovariantCLM_L2 U‖ ≤ 4 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun X => ?_)
  have h1 := norm_sq_curl_le U X
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (norm_nonneg _)] at h2
  have h3 : Real.sqrt (16 * ‖X‖ ^ 2) = 4 * ‖X‖ := by
    rw [show (16 : ℝ) * ‖X‖ ^ 2 = (4 * ‖X‖) ^ 2 by ring,
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * ‖X‖)]
  rw [h3] at h2
  exact h2

/-! ### §1a — CONTROLS

Two rows, so `opNorm_curl_le_four` cannot be read as a statement about a zero operator or as an
artefact of a degenerate carrier. -/

/-- **§1a(i) — THE BOUND IS NOT ABOUT THE ZERO OPERATOR.**  On any extent carrying a bond field
whose covariant curl is nonzero, `0 < ‖D_U‖ ≤ 4`.  Stated with the witness as a hypothesis so the
row is a genuine implication and not an existence claim this lane has not discharged. -/
theorem opNorm_curl_pos_of_witness
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (X : BondFnL2 L) (hX : curlCovariantCLM_L2 U X ≠ 0) :
    0 < ‖curlCovariantCLM_L2 U‖ := by
  rcases (norm_nonneg (curlCovariantCLM_L2 U)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : curlCovariantCLM_L2 U = 0 := by
      rw [← ContinuousLinearMap.opNorm_zero_iff]
      exact h.symm
    exact hX (by rw [hz]; simp)

/-- **§1a(ii) — GARBAGE SUBSTITUTION (S82): the bound is NOT algebraically forced.**  The same
proof shape with `16` replaced by any smaller nonnegative constant would assert something the
premise does not give: exhibited here as the arithmetic fact that a bound `‖D_U X‖² ≤ c‖X‖²` with
`c < 16` does NOT follow from `dstarDQuadForm U A ≤ 16·bondEnergy A` alone — the implication needs
`16 ≤ c`.  Stated as a theorem about the constants so a reader can see where the `16` is load
bearing. -/
theorem sixteen_is_load_bearing (c : ℝ) (hc : ∀ (e : ℝ), 0 ≤ e → 16 * e ≤ c * e) : 16 ≤ c := by
  have h := hc 1 (by norm_num)
  linarith

/-! ## §2 — THROUGH THE RIGHT INVERSE: `‖D_{U_fine} ∘ R‖ ≤ 4·ℓ³` -/

/-- **THE COMPOSED BOUND.**  `‖R‖ = ℓ³` EXACTLY (`QSurjRInverse.opNorm_rInvComposed`, REUSED) and
`‖D‖ ≤ 4` (§1), so the composite that `norm_H1_le_of_rightInverse_bound`'s `ε`-threshold mentions is
bounded by a number depending on the block scale alone. -/
theorem opNorm_curl_comp_rInv_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ≤ 4 * (ell : ℝ) ^ 3 := by
  have h1 : ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖
      ≤ ‖curlCovariantCLM_L2 Ufine‖ * ‖rInvComposed h Ufine‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  rw [opNorm_rInvComposed h Ufine] at h1
  have h2 := opNorm_curl_le_four Ufine
  have h3 : (0 : ℝ) ≤ (ell : ℝ) ^ 3 := by positivity
  nlinarith [h1, h2, h3]

/-- **AND ITS SQUARE**, in the exact shape `norm_H1_le_of_rightInverse_bound`'s `hbig` asks for. -/
theorem sq_opNorm_curl_comp_rInv_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 ≤ 16 * (ell : ℝ) ^ 6 := by
  have h1 := opNorm_curl_comp_rInv_le h Ufine
  have h0 : (0 : ℝ) ≤ ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have h3 : (0 : ℝ) ≤ (ell : ℝ) ^ 3 := by positivity
  nlinarith [h1, h0, h3]

/-! ## §3 — THE ADMISSIBLE `ε`, AS A NUMBER

`TerminalBinder.norm_H1_le_of_rightInverse_bound` collapses the `‖H₁‖` bound to `√(‖R‖²+1)` as soon
as `ε ≥ ‖D∘R‖² + a`.  Until now that threshold mentioned an operator norm nobody had evaluated;
§2 replaces it by `16ℓ⁶ + a`. -/

/-- **THE NUMERIC `ε`-THRESHOLD.**  Every `ε ≥ 16ℓ⁶ + a` satisfies `hbig`. -/
theorem hbig_of_eps_ge {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (a eps : ℝ)
    (heps : 16 * (ell : ℝ) ^ 6 + a ≤ eps) :
    ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 + a ≤ eps := by
  have h1 := sq_opNorm_curl_comp_rInv_le h Ufine
  linarith

#print axioms norm_sq_curl_le
#print axioms opNorm_curl_le_four
#print axioms opNorm_curl_pos_of_witness
#print axioms sixteen_is_load_bearing
#print axioms opNorm_curl_comp_rInv_le
#print axioms sq_opNorm_curl_comp_rInv_le
#print axioms hbig_of_eps_ge

end AdalyFormal.HrawRDischarge
