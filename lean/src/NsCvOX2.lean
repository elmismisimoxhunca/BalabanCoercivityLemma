import NsCvOX1
import NsCvOF19

/-!
# CvOX2 -- `NearUnits` without the Dirichlet conjunct (lane omega, extra)

`WellDefG = (H0 bijective, G1inv unit, N unit) and (DelpA unit, Ginv unit, QGQ* unit)`; the unit `DelpA + (1 - mask)` holds for
every configuration (CvOX1), so it is dropped from the unit hypothesis:
`NearUnitsRest` (five conjuncts) implies `NearUnits`, and `not_WDH_of_nearUnitsRest` is the refutation under the weaker hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

/-- the five units that are NOT automatic. -/
def UnitsRest (P : IngrBParams) : Prop :=
  Function.Bijective (H0 P.Lam P.Q1) ∧ IsUnit P.G1inv ∧ IsUnit (GenP.Nmat P) ∧ IsUnit P.data.Ginv ∧
    IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs)

/-- arbitrarily close above the crossing, the five non-automatic units hold. -/
def NearUnitsRest (ell M R : ℕ) (hell : 0 < ell) (a cs : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < tcap ell ∧ cs < Real.cos t ∧ Real.cos t < cs + ε ∧
    UnitsRest (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R))

theorem nearUnits_of_rest {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (a cs : ℝ) (ha : 0 < a)
    (h : NearUnitsRest ell M R (by omega) a cs) : NearUnits ell M R (by omega) a cs := by
  intro ε hε
  obtain ⟨t, h1, h2, h3, hr⟩ := h ε hε
  refine ⟨t, h1, h2, h3, ⟨⟨hr.1, hr.2.1, hr.2.2.1⟩, ?_, hr.2.2.2.1, hr.2.2.2.2⟩⟩
  have hout : ∃ x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), x ∉ (geomOf ell 2 (neS ell M R)).Om0 := by
    refine ⟨fun _ => 0, fun hmem => ?_⟩
    simp only [geomOf, Set.mem_setOf_eq] at hmem
    have h0 := ((neS_om0 (ell := ell) (M := M) (R := R) (fun _ => 0)).mp hmem).1
    have hp := ne_P0_pos hell3 hM hR
    simp at h0
    omega
  exact delpA_unit (geomOf ell 2 (neS ell M R)) (stagU ell M R t) ha (by show 2 ≤ ell; omega) hout

/-- **the refutation under the weaker hypothesis** (five non-automatic units near the crossing). -/
theorem not_WDH_of_nearUnitsRest (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      ∃ cs : ℝ, IsCrossingN ell (ell ^ m) R cs ∧ NearUnitsRest ell (ell ^ m) R (by omega) a cs) :
    FailEllC CfData.cf ell (by omega) a := by
  refine not_WDH_of_nearUnits ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, cs, hcs, hnu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  exact ⟨R, le_trans (le_max_left _ _) hRR, cs, hcs,
    nearUnits_of_rest hell3 hM (le_trans (le_max_right _ _) hRR) a cs ha hnu⟩

#print axioms nearUnits_of_rest
#print axioms not_WDH_of_nearUnitsRest

end AdalyFormal.CoverOmega
