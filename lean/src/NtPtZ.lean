import NtPtQ5

/-!
# PtZ -- the four units hold at the flat point `t = 0` of the nested staggered path (lane omega/near2/point)

`unitsFour_flat`: for `3 ≤ ell`, `ell ∣ M`, `0 < M`, `1 ≤ R` and every `a > 0`, `UnitsFour` holds for `gparams ell 2 (neLu M R) _ (neS ell M R) (stagU ell M R 0) a (neLam M R)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG

theorem stagU_zero_flat (ell M R : ℕ) : stagU ell M R 0 = flatCfg := stagCfg_zero _

theorem unitsFour_flat {ell M R : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) (ha : 0 < a) :
    UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stagU ell M R 0) a (neLam M R)) := by
  have hP : PGeo ell M R := pgeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  rw [stagU_zero_flat]
  exact pt_unitsFour (PF ell M R hell a) rfl (fun x h0 => ginv_definite hP hell a ha x h0) (qs_injective hP hell a)

/-- the same, with the hypotheses of `AnUnits4`'s regime (parity is not needed). -/
theorem unitsFour_flat_regime {ell M R : ℕ} (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    (a : ℝ) (ha : 0 < a) :
    UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stagU ell M R 0) a (neLam M R)) :=
  unitsFour_flat hell3 hdvd hM hR a ha

#print axioms unitsFour_flat

end AdalyFormal.CoverOmega
