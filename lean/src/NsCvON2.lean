import NsCvON1

/-!
# CvON2 -- `AnUnits` (analytic proxy for the five units) gives `NearUnitsRest`, and refutes `P428Target8NCWDH` (lane omega/near)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace Topology
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

/-- the five non-automatic units hold wherever a real-analytic proxy `D` on `(-tcap ell, tcap ell)` is nonzero, and `D` is nonzero somewhere. -/
def AnUnits (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ D : ℝ → ℝ, AnalyticOnNhd ℝ D (Ioo (-tcap ell) (tcap ell)) ∧ (∃ t0 ∈ Ioo (-tcap ell) (tcap ell), D t0 ≠ 0) ∧
    ∀ t : ℝ, |t| < tcap ell → D t ≠ 0 →
      UnitsRest (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R))

theorem nearUnitsRest_of_anUnits {ell M R : ℕ} (hell : 0 < ell) (a cs : ℝ) (hcs1 : Real.cos (tcap ell) < cs) (hcs2 : cs < 1)
    (h : AnUnits ell M R hell a) : NearUnitsRest ell M R hell a cs := by
  obtain ⟨D, hD, ⟨t0, ht0, hD0⟩, hu⟩ := h
  intro ε hε
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_nonzero_near_cos (tcap ell) (tcap_pos ell) (tcap_le_pi ell) D hD t0 ht0 hD0 cs hcs1 hcs2 ε hε
  exact ⟨t, h1, h2, h3, hu t h1 h4⟩

/-- **the refutation of `P428Target8NCWDH` from generic-in-`t` units**: for `ell` with `StagOK ell`, `3 <= ell`, some `a > 0`, infinitely many `m`
and for each infinitely many `R`, `AnUnits`. -/
theorem not_WDH_of_anUnits (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ AnUnits ell (ell ^ m) R (by omega) a) :
    FailEllC CfData.cf ell (by omega) a := by
  refine not_WDH_of_nearUnitsRest ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hA⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  have hMe : ell ≤ ell ^ m := Nat.le_of_dvd hM hdvd
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hRR
  obtain ⟨cs, hcs, hcs1, -⟩ := nested_stag_failAt hell3 hE hdvd hMe hM hR1 a
  exact ⟨R, le_trans (le_max_left _ _) hRR, cs, hcs, nearUnitsRest_of_anUnits (ell := ell) (M := ell ^ m) (R := R) (by omega) a cs hcs1 hcs.1 hA⟩

#print axioms exists_nonzero_near_cos
#print axioms nearUnitsRest_of_anUnits
#print axioms not_WDH_of_anUnits

end AdalyFormal.CoverOmega
