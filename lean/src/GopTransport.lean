/-
Owned SI1 L3g scratch file (compute/m1_si1_l3g/gop/). Imports the frozen `AdalyFormal` package
read-only, plus the READ-ONLY paid `deps/M2RouteAudit.lean` (ambient M2 series machinery:
`gOpM2`, `adM2`, `hCoeff`, `hSummable`, `ambient_series_summable`, `gOpM2_neg_adM2`,
`adM2_pow_coe`) and `deps/T1MainSegment.lean` (`OneStep124.adOp/gOp/gCoeff` on `SuTwo`). Neither
dep file is edited.

SCOPE: only the transport/identification lemma requested by the L3g follow-up — no
`dexp_eq_gOp` assembly, no `Bch2`/`RegularityGap` imports, no `hasSum_Q1/Q2`, no `HasDerivAt`
points. Uses M2RouteAudit's PAID generic `hCoeff`/`hSummable`/`ambient_series_summable`/
`gOpM2_neg_adM2`/`adM2_pow_coe` directly rather than re-deriving them; the only NEW work here is
identifying `gOpM2 (-adM2 Z) (v:M2)` (ambient tsum, applied) with `(gOp (-(adOp Z)) v : SuTwo) :
M2` (SuTwo-level tsum, applied, then coerced) via coercion of finite powers (`adM2_pow_coe`, paid)
followed by pushing the tsum through the `SuTwo ↪ M2` coercion (`Submodule.subtypeL`).
-/
import T1MainSegment
import NonzeroExpDeriv
import M2RouteAudit

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace AdalySI1.GopTransport

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open OneStep124 (adOp gOp gCoeff)
open AdalySI1.M2RouteAudit

/-! ## §1 — the sign-coefficient identity, instantiated at `SuTwo →L[ℝ] SuTwo`

`M2RouteAudit.gCoeff_neg_pow_smul` is stated only for `T : M2 →L[ℝ] M2`; `gOp`'s argument here is
`-(adOp Z) : SuTwo →L[ℝ] SuTwo`, so the same short generic argument is reproved at this instance
(no ambient content, purely algebraic on the bundled endomorphism, so this is not "owed" transport
work, just an instantiation the paid file does not itself supply). -/

theorem gCoeff_neg_pow_smul_suTwo (T : SuTwo →L[ℝ] SuTwo) (n : ℕ) :
    gCoeff n • (-T) ^ n = hCoeff n • T ^ n := by
  have hneg : (-T) ^ n = ((-1 : ℝ) ^ n) • T ^ n := by
    suffices h : ∀ x, ((-T) ^ n) x = (((-1 : ℝ) ^ n) • T ^ n) x by
      exact ContinuousLinearMap.ext h
    induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      simp only [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.smul_apply, ih, map_neg, smul_neg, smul_smul, neg_smul]
      module
  have hcoeff : gCoeff n * (-1 : ℝ) ^ n = hCoeff n := by
    rw [gCoeff, hCoeff, div_mul_eq_mul_div, ← mul_pow]
    norm_num
  rw [hneg, smul_smul, hcoeff]

/-! ## §2 — `gOp (-(adOp Z)) v` as a `SuTwo`-level pointwise tsum -/

theorem gOp_apply_eq_tsum (Z v : SuTwo) :
    (gOp (-(adOp Z)) v : SuTwo) = ∑' n : ℕ, hCoeff n • (((adOp Z) ^ n) v) := by
  have step1 : (gOp (-(adOp Z)) v : SuTwo) = (∑' n : ℕ, hCoeff n • (adOp Z) ^ n) v := by
    show (∑' n : ℕ, gCoeff n • (-(adOp Z)) ^ n) v = _
    congr 1
    exact tsum_congr (fun n => gCoeff_neg_pow_smul_suTwo (adOp Z) n)
  rw [step1]
  exact (ContinuousLinearMap.apply ℝ SuTwo v).map_tsum (hSummable (adOp Z))

theorem suTwo_series_summable (Z v : SuTwo) :
    Summable (fun n : ℕ => hCoeff n • (((adOp Z) ^ n) v)) :=
  (ContinuousLinearMap.apply ℝ SuTwo v).summable (hSummable (adOp Z))

/-! ## §3 — the transport/identification theorem -/

/-- The owed transport lemma: `M2RouteAudit`'s ambient `gOpM2` series, evaluated at the coerced
basepoint, agrees with `OneStep124.gOp (-(adOp Z))` on `SuTwo`, coerced. Assembled from PAID
ambient facts (`gOpM2_neg_adM2`, `ambient_series_summable`, `adM2_pow_coe`) plus finite-power
coercion and one push of `tsum` through the `SuTwo ↪ M2` continuous linear inclusion. -/
theorem gOpM2_apply_coe_eq_gOp (Z v : SuTwo) :
    (gOpM2 (-adM2 (Z : M2))) (v : M2) = ((gOp (-(adOp Z)) v : SuTwo) : M2) := by
  have hM2eq : (gOpM2 (-adM2 (Z : M2))) (v : M2)
      = ∑' n : ℕ, hCoeff n • ((adM2 (Z : M2)) ^ n) (v : M2) := by
    have step1 : (gOpM2 (-adM2 (Z : M2))) = ∑' n : ℕ, hCoeff n • (adM2 (Z : M2)) ^ n :=
      gOpM2_neg_adM2 (Z : M2)
    rw [step1]
    exact (ContinuousLinearMap.apply ℝ M2 (v : M2)).map_tsum (ambient_series_summable (Z : M2))
  rw [hM2eq]
  have hterm : ∀ n : ℕ, hCoeff n • ((adM2 (Z : M2)) ^ n) (v : M2)
      = ((hCoeff n • (((adOp Z) ^ n) v) : SuTwo) : M2) := by
    intro n
    rw [adM2_pow_coe Z v n, Submodule.coe_smul]
  rw [tsum_congr hterm]
  have hSuHasSum : HasSum (fun n : ℕ => hCoeff n • (((adOp Z) ^ n) v)) (gOp (-(adOp Z)) v) := by
    rw [gOp_apply_eq_tsum Z v]
    exact (suTwo_series_summable Z v).hasSum
  exact (hSuHasSum.mapL (Submodule.subtypeL SuTwo)).tsum_eq

#print axioms gOpM2_apply_coe_eq_gOp

end AdalySI1.GopTransport
