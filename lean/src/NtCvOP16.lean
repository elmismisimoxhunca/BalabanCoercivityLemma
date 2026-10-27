import NtCvOP15

/-!
# CvOP16 -- `Dstruct` is real-analytic on `(-tcap ell, tcap ell)` (lane omega/near2/struct)

`dstruct_analytic`: for `3 ≤ ell`, `StagOK ell`, `ell ∣ M`, `0 < M`, `1 ≤ R`, `0 < a`, the proxy `Dstruct ell M R hell a` is analytic on
`(-tcap ell, tcap ell)`; with `anUnits4_of_dstruct` (CvOS12) this gives `AnUnits4` from `∃ t0, Dstruct t0 ≠ 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

theorem dstruct_analytic {ell M R : ℕ} (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    (hell : 0 < ell) {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℝ (Dstruct ell M R hell a) (Ioo (-tcap ell) (tcap ell)) := by
  intro t0 ht0
  have htπ : |t0| < tcap ell := abs_lt.2 ⟨ht0.1, ht0.2⟩
  have S := nested_stagSetup hell3 hE hdvd hM hR
  have hT : TowerOK (geomOf ell 2 (neS ell M R)) (stagU ell M R) t0 :=
    tower_stag_ana S.hN S.hE S.hell (neC ell M R) S.hc1 S.hc2 htπ
  have hU : LinkEA (stagU ell M R) t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hJ := JfOf_analytic hU (plaqIn (geomOf ell 2 (neS ell M R)).Om0)
  have hout := out_nested hell3 hM hR hell a t0
  have h := DstructG_analytic (geomOf ell 2 (neS ell M R)) (stagU ell M R) hT (le_of_eq S.hk) ha
    (by show 2 ≤ ell; omega) hout _ hJ
  exact h

#print axioms dstruct_analytic

/-- **the structural half, composed**: a point with the four units and `gOf ≠ 0` makes `AnUnits4` true. -/
theorem anUnits4_of_point {ell M R : ℕ} (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    (hell : 0 < ell) {a : ℝ} (ha : 0 < a) (t0 : ℝ) (ht0 : |t0| < tcap ell)
    (hg : gOf (PN ell M R hell a t0).G (PN ell M R hell a t0).U ≠ 0) (hu : UnitsFour (PN ell M R hell a t0)) :
    AnUnits4 ell M R hell a :=
  anUnits4_of_dstruct hell3 hM hR hell a (dstruct_analytic hell3 hE hdvd hM hR hell ha)
    ⟨t0, abs_lt.1 ht0, dstruct_ne_zero_of_units hell3 hM hR hell a t0 hg hu⟩

#print axioms anUnits4_of_point

end AdalyFormal.CoverOmega.Struct
