import NsCvOS15
import NsPtZ

/-!
# NsCvOS16 -- final composition at cube factor `cf`, `ell` even or odd `≥ 5` (`StagOK ell`) (lane ncwdh_strong_20261017)

`PtZ.unitsFour_flat_regime` (point lane) gives the four units at `t = 0` for every `3 ≤ ell`, `M = ell^m`, every `R >= 1`, every `a > 0`;
`not_WDH_of_unitsFour_points` (CvOS15, through `dstruct_analytic`, `gOf_PN_ne_zero`) turns one such point per `(m, R)` into `FailEllC`.
* `failEllC_ok`        : `FailEllC cf ell _ a`  for the instance factor `cf`, every `3 ≤ ell` with `StagOK ell`, every `a > 0`;
* `failsAtEll_ok`      : `∀ c ≥ 10, ∀ ell ≥ 3 with StagOK ell, ∀ a > 0, FailsAtEll c ell a`  (the per-ell, per-factor strong form).
-/
set_option autoImplicit false

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.NcwdhStrong

theorem failEllC_ok (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a) :
    FailEllC CfData.cf ell (by omega) a := by
  refine not_WDH_of_unitsFour_points ell hell3 hE a ha ?_
  intro m₀
  refine ⟨m₀ + 1, by omega, fun R₀ => ⟨R₀ + 1, by omega, 0, by rw [abs_zero]; exact tcap_pos ell, ?_⟩⟩
  have hdvd : ell ∣ ell ^ (m₀ + 1) := dvd_pow_self ell (by omega)
  exact AdalyFormal.CoverOmega.unitsFour_flat_regime (ell := ell) (M := ell ^ (m₀ + 1)) (R := R₀ + 1)
    hell3 hE hdvd (pow_pos (by omega) _) (by omega) a ha

omit [CfData] in
theorem failsAtEll_ok (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell (by omega) a := by
  letI : CfData := ⟨c, hc⟩
  exact failsAtEll_of_failEllC (by omega) (by omega) (failEllC_ok ell hell3 hE a ha)

omit [CfData] in
/-- the coverage-free headline at every cube factor `c ≥ 10` is false. -/
theorem not_P428Target8NCWDHc (c : ℕ) (hc : 10 ≤ c) : ¬ P428Target8NCWDHc c :=
  not_target_of_failsAtEll (ell := 4) (a := 1) one_pos (failsAtEll_ok c hc 4 (by norm_num) (Or.inl (by norm_num)) 1 one_pos)

#print axioms failEllC_ok
#print axioms failsAtEll_ok
#print axioms not_P428Target8NCWDHc

end AdalyFormal.CoverOmega.Struct
