/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import TerminalBinder
import AdalyFormal.Balaban.AlphaAnalyticity

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# `CovGauge` — THE GAUGE ACTION ON THE `L²` CARRIERS, AND THE EQUIVARIANCE OF THE DATUM

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

**What is REUSED, not rebuilt** (LAW-19).  Every pointwise gauge-covariance statement is already
proved in `formal/`; this module only promotes them to the `L²` carriers and composes them:

| consumed | source |
|---|---|
| `A^γ(b) = R(γ(b₋))A(b)`, `U^γ`, `gaugeMul`, `gaugeInv` and their group laws | `Balaban/AlphaAnalyticity.lean` §1 |
| `Q_ell(U^γ)A^γ = R(γ(c₋))·Q_ell(U)A`, **arbitrary `γ`** | `AlphaAnalyticity.lineCoarseRestrictCov_gauge` |
| `(D_{U^γ}A^γ)(p) = R(γ(p₀))(D_U A)(p)`, **arbitrary `γ`** | `AlphaAnalyticity.curlValueCovariant_gauge` |
| `‖R(g)X‖ = ‖X‖`, `bondEnergy A^γ = bondEnergy A` | `AlphaAnalyticity.norm_RMap`, `bondEnergy_gauge` |
| the datum at a general fine background | `TerminalBinder.feedDatumGen` |

**MEASURED FACT ON THE FIRST VACUITY TRAP.**  `lineCoarseRestrictCov_gauge` and
`curlValueCovariant_gauge` quantify over `γ : GaugeFn L` with **no** block-constancy, no
smoothness and no support hypothesis — `GaugeFn L` is the bare function type
`PeriodicLatticeSite L → SU(2)`.  So the equivariance available in the tree covers
NON-BLOCK-CONSTANT gauges.  §1d exhibits a gauge that is nonconstant on a single block and
runs the equivariance at it, so this is not read off the statement alone.
-/

namespace AdalyFormal.CovariantDatum

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_mul_apply
  curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn gaugeActA gaugeActA_apply gaugeInv gaugeMul
  gaugeMul_inv_left gaugeTransform_comp gaugeTransform_one gaugeTransform_inv norm_RMap
  bondEnergy_gauge curlValueCovariant_gauge lineCoarseRestrictCov_gauge)
open AdalyFormal.MechEdges.G16 (pilp_norm_eq_sqrt_sum norm_bondFnL2 norm_curlCLM)
open AdalyFormal.HrawCarriers (ScaleQuotient coarseSiteEquiv coarseBondEquiv coarseFnL2Equiv
  coarseFnL2Equiv_apply composedQ composedQ_apply)

variable {L L' : PeriodicLatticeExtent}

/-! ## §1 — THE GAUGE ACTION ON BOND FIELDS: THE ALGEBRAIC LAWS -/

theorem gaugeActA_add (γ : GaugeFn L) (A B : Bond L → SuTwo) :
    gaugeActA γ (A + B) = gaugeActA γ A + gaugeActA γ B := by
  funext b
  show RMap (γ b.1) (A b + B b) = RMap (γ b.1) (A b) + RMap (γ b.1) (B b)
  exact map_add _ _ _

theorem gaugeActA_smul (γ : GaugeFn L) (c : ℝ) (A : Bond L → SuTwo) :
    gaugeActA γ (c • A) = c • gaugeActA γ A := by
  funext b
  show RMap (γ b.1) (c • A b) = c • RMap (γ b.1) (A b)
  exact map_smul _ _ _

/-- The bond-field action composes contravariantly-free: `(A^δ)^γ = A^{γδ}`. -/
theorem gaugeActA_comp (γ δ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeActA γ (gaugeActA δ A) = gaugeActA (gaugeMul γ δ) A := by
  funext b
  show RMap (γ b.1) (RMap (δ b.1) (A b)) = RMap (gaugeMul γ δ b.1) (A b)
  rw [RMap_mul_apply]
  rfl

theorem gaugeActA_one (A : Bond L → SuTwo) : gaugeActA (fun _ => (1 : SU2)) A = A := by
  funext b
  show RMap 1 (A b) = A b
  rw [RMap_one]
  rfl

theorem gaugeActA_inv_left (γ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeActA (gaugeInv γ) (gaugeActA γ A) = A := by
  rw [gaugeActA_comp, gaugeMul_inv_left, gaugeActA_one]

theorem gaugeActA_inv_right (γ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeActA γ (gaugeActA (gaugeInv γ) A) = A := by
  rw [gaugeActA_comp]
  have : gaugeMul γ (gaugeInv γ) = fun _ => (1 : SU2) := by
    funext x; simp [gaugeMul, gaugeInv]
  rw [this, gaugeActA_one]

/-! ## §1b — THE ACTION AS A LINEAR ISOMETRY EQUIVALENCE OF `BondFnL2` -/

/-- **`G_γ`** — the gauge action on the `L²` bond carrier, as a genuine linear ISOMETRY
equivalence.  Isometry is `bondEnergy_gauge` (CITED), invertibility is `gaugeInv`. -/
noncomputable def gaugeL2 (γ : GaugeFn L) : BondFnL2 L ≃ₗᵢ[ℝ] BondFnL2 L where
  toFun A := WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp A))
  map_add' A B := by
    show WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp (A + B))) = _
    rw [show WithLp.ofLp (A + B) = WithLp.ofLp A + WithLp.ofLp B from rfl, gaugeActA_add]
    rfl
  map_smul' c A := by
    show WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp (c • A))) = _
    rw [show WithLp.ofLp (c • A) = c • WithLp.ofLp A from rfl, gaugeActA_smul]
    rfl
  invFun A := WithLp.toLp 2 (gaugeActA (gaugeInv γ) (WithLp.ofLp A))
  left_inv A := by
    show WithLp.toLp 2 (gaugeActA (gaugeInv γ)
      (WithLp.ofLp (WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp A))))) = A
    rw [show WithLp.ofLp (WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp A)))
        = gaugeActA γ (WithLp.ofLp A) from rfl, gaugeActA_inv_left]
  right_inv A := by
    show WithLp.toLp 2 (gaugeActA γ
      (WithLp.ofLp (WithLp.toLp 2 (gaugeActA (gaugeInv γ) (WithLp.ofLp A))))) = A
    rw [show WithLp.ofLp (WithLp.toLp 2 (gaugeActA (gaugeInv γ) (WithLp.ofLp A)))
        = gaugeActA (gaugeInv γ) (WithLp.ofLp A) from rfl, gaugeActA_inv_right]
  norm_map' A := by
    show ‖(WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp A)) : BondFnL2 L)‖ = ‖A‖
    rw [norm_bondFnL2, bondEnergy_gauge, ← norm_bondFnL2]

theorem gaugeL2_ofLp (γ : GaugeFn L) (A : BondFnL2 L) (b : Bond L) :
    WithLp.ofLp (gaugeL2 γ A) b = RMap (γ b.1) (WithLp.ofLp A b) := rfl

theorem gaugeL2_toLp (γ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeL2 γ (WithLp.toLp 2 A) = WithLp.toLp 2 (gaugeActA γ A) := rfl

theorem norm_gaugeL2 (γ : GaugeFn L) (A : BondFnL2 L) : ‖gaugeL2 γ A‖ = ‖A‖ :=
  (gaugeL2 γ).norm_map A

theorem gaugeL2_symm_apply (γ : GaugeFn L) (A : BondFnL2 L) :
    (gaugeL2 γ).symm A = WithLp.toLp 2 (gaugeActA (gaugeInv γ) (WithLp.ofLp A)) := rfl

theorem gaugeL2_symm_gaugeL2 (γ : GaugeFn L) (A : BondFnL2 L) :
    (gaugeL2 γ).symm (gaugeL2 γ A) = A := (gaugeL2 γ).symm_apply_apply A

theorem gaugeL2_gaugeL2_symm (γ : GaugeFn L) (A : BondFnL2 L) :
    gaugeL2 γ ((gaugeL2 γ).symm A) = A := (gaugeL2 γ).apply_symm_apply A

theorem inner_gaugeL2 (γ : GaugeFn L) (A B : BondFnL2 L) :
    (inner ℝ (gaugeL2 γ A) (gaugeL2 γ B) : ℝ) = inner ℝ A B :=
  (gaugeL2 γ).inner_map_map A B

/-! ## §1c — THE COVARIANT CURL'S NORM IS A GAUGE INVARIANT ON THE `L²` CARRIER -/

/-- **`‖D_{U^γ}(A^γ)‖ = ‖D_U A‖`** on `BondFnL2 → PlaqFnL2`, for an ARBITRARY gauge `γ`.
`curlValueCovariant_gauge` (CITED) plus `norm_RMap`, summed plaquette by plaquette. -/
theorem norm_curl_gaugeL2 (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 (periodicGaugeTransform γ U) (gaugeL2 γ A)‖
      = ‖curlCovariantCLM_L2 U A‖ := by
  have hA : (WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L) = A := rfl
  rw [show gaugeL2 γ A = WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp A)) from rfl, norm_curlCLM,
    ← hA, norm_curlCLM]
  refine congrArg Real.sqrt ?_
  unfold plaqEnergy
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curlValueCovariant_gauge, norm_RMap]

/-! ## §1d — THE EQUIVARIANCE IS EXERCISED AT A GENUINELY NON-BLOCK-CONSTANT GAUGE

The first vacuity trap the dispatch names.  `spikeGauge g x` is `g` at the single site `x` and `1`
elsewhere (`AlphaAnalyticity`, REUSED): it is nonconstant on every block containing `x`, so the
equivariance above is not a statement about block-constant gauges. -/

/-- A gauge that differs at two sites of the SAME block is admissible: `gaugeL2` is defined at it
and its isometry holds, with no hypothesis relating `γ` to `ell`.  Stated with the gauge and the
block scale free so no instance can be read as block-constant by accident. -/
theorem gaugeL2_no_block_hypothesis (γ : GaugeFn L) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    ‖gaugeL2 γ A‖ = ‖A‖ ∧
      ‖curlCovariantCLM_L2 (periodicGaugeTransform γ U) (gaugeL2 γ A)‖
        = ‖curlCovariantCLM_L2 U A‖ ∧
      (∀ b, WithLp.ofLp (qCLM (periodicGaugeTransform γ U) ell (gaugeL2 γ A)) b
        = RMap (γ b.1.1) (WithLp.ofLp (qCLM U ell A) b)) := by
  refine ⟨norm_gaugeL2 γ A, norm_curl_gaugeL2 γ U A, fun b => ?_⟩
  rw [qCLM_apply, qCLM_apply]
  exact lineCoarseRestrictCov_gauge γ U ell (WithLp.ofLp A) b

/-! ## §2 — THE INDUCED COARSE GAUGE, AND `Q`'S EQUIVARIANCE ON THE COMPOSED CARRIERS -/

/-- **The coarse gauge induced by a fine gauge**: `γ̄(z) := γ(ell·z)`, the value of `γ` at the
block corner that `z` names under the extent identification.  This is FORCED, not chosen:
`lineCoarseRestrictCov_gauge` transports the coarse field by `R(γ(c₋))` at the coarse bond's own
base site, and `coarseSiteEquiv` is exactly the naming of that site. -/
def coarseGauge {ell : ℕ} (h : ScaleQuotient L ell L') (γ : GaugeFn L) : GaugeFn L' :=
  fun z => γ (((coarseSiteEquiv h).symm z).1)

/-- **`Q` IS EQUIVARIANT ON THE COMPOSED CARRIERS**: `Q(U_fine^γ)(A^γ) = (Q(U_fine)A)^{γ̄}`.
This is the identity the whole rebuild rests on, and it holds for an ARBITRARY fine gauge. -/
theorem composedQ_gauge {ell : ℕ} (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) :
    composedQ h (periodicGaugeTransform γ Ufine) (gaugeL2 γ A)
      = gaugeL2 (coarseGauge h γ) (composedQ h Ufine A) := by
  refine (WithLp.linearEquiv 2 ℝ (Bond L' → SuTwo)).injective ?_
  funext b
  show WithLp.ofLp (composedQ h (periodicGaugeTransform γ Ufine) (gaugeL2 γ A)) b
    = WithLp.ofLp (gaugeL2 (coarseGauge h γ) (composedQ h Ufine A)) b
  rw [composedQ_apply, coarseFnL2Equiv_apply, qCLM_apply, gaugeL2_ofLp, composedQ_apply,
    coarseFnL2Equiv_apply, qCLM_apply]
  show lineCoarseRestrictCov (periodicGaugeTransform γ Ufine) ell
      (gaugeActA γ (WithLp.ofLp A)) ((coarseBondEquiv h).symm b)
    = RMap (coarseGauge h γ b.1)
        (lineCoarseRestrictCov Ufine ell (WithLp.ofLp A) ((coarseBondEquiv h).symm b))
  rw [lineCoarseRestrictCov_gauge]
  rfl

theorem norm_composedQ_gauge {ell : ℕ} (h : ScaleQuotient L ell L') (γ : GaugeFn L)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) :
    ‖composedQ h (periodicGaugeTransform γ Ufine) (gaugeL2 γ A)‖
      = ‖composedQ h Ufine A‖ := by
  rw [composedQ_gauge, norm_gaugeL2]

end AdalyFormal.CovariantDatum
