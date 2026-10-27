import NsCvON4
import NsCvON2

/-!
# CvON5 -- generic-in-`t` reduction with `H0` discharged: four units remain (lane omega/near)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

/-- the four units that remain after `H0` (`Pn_H0_bijective`) and the Dirichlet unit (`delpA_unit`). -/
def UnitsFour (P : IngrBParams) : Prop :=
  IsUnit P.G1inv ∧ IsUnit (GenP.Nmat P) ∧ IsUnit P.data.Ginv ∧ IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs)

/-- four units hold wherever a real-analytic proxy on `(-tcap ell, tcap ell)` is nonzero, and the proxy is nonzero somewhere. -/
def AnUnits4 (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ D : ℝ → ℝ, AnalyticOnNhd ℝ D (Ioo (-tcap ell) (tcap ell)) ∧ (∃ t0 ∈ Ioo (-tcap ell) (tcap ell), D t0 ≠ 0) ∧
    ∀ t : ℝ, |t| < tcap ell → D t ≠ 0 →
      UnitsFour (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R))

/-- `H0` of the nested staggered family is bijective wherever an analytic proxy on `(-tcap, tcap)` is nonzero, and the proxy is nonzero somewhere. -/
def H0Good (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ dH : ℝ → ℝ, AnalyticOnNhd ℝ dH (Ioo (-tcap ell) (tcap ell)) ∧ (∃ t1 ∈ Ioo (-tcap ell) (tcap ell), dH t1 ≠ 0) ∧
    ∀ t : ℝ, |t| < tcap ell → dH t ≠ 0 → Function.Bijective (H0 (neLam M R) (Pn ell M R hell a t).Q1)

theorem anUnits_of_four {ell M R : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ)
    (hH : H0Good ell M R (by omega) a) (h : AnUnits4 ell M R (by omega) a) : AnUnits ell M R (by omega) a := by
  obtain ⟨D, hD, ⟨t0, ht0, hD0⟩, hu⟩ := h
  obtain ⟨dH, hdH, ⟨t1, ht1, hdH1⟩, hbij⟩ := hH
  obtain ⟨t2, ht2, hne⟩ := exists_mul_ne_zero hD hdH ht0 ht1 hD0 hdH1
  refine ⟨fun t => D t * dH t, hD.mul hdH, ⟨t2, ht2, hne⟩, fun t htπ hDt => ?_⟩
  have hD1 : D t ≠ 0 := left_ne_zero_of_mul hDt
  have hD2 : dH t ≠ 0 := right_ne_zero_of_mul hDt
  exact ⟨hbij t htπ hD2, hu t htπ hD1⟩

/-- **the refutation of `P428Target8NCWDH` from generic-in-`t` G1inv / N / Ginv / QGQ* units.** -/
theorem not_WDH_of_anUnits4 (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ H0Good ell (ell ^ m) R (by omega) a ∧ AnUnits4 ell (ell ^ m) R (by omega) a) :
    FailEllC CfData.cf ell (by omega) a := by
  refine not_WDH_of_anUnits ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hH, hA⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    anUnits_of_four hell3 hdvd hM (le_trans (le_max_right _ _) hRR) a hH hA⟩

#print axioms anUnits_of_four
#print axioms not_WDH_of_anUnits4

end AdalyFormal.CoverOmega
