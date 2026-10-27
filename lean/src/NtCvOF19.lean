import NtCvOF18

/-!
# CvOF19 -- `NearUnits` at the crossing gives `FailAt`; infinitely many `(m, R)` refute `P428Target8NCWDH` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

variable {ell M R : ℕ}

theorem nested_stag_failAt (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hMe : ell + 3 ≤ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    ∃ cs : ℝ, IsCrossingN ell M R cs ∧ Real.cos (tcap ell) < cs ∧ (NearUnits ell M R (by omega) a cs → FailAtC CfData.cf ell M R (by omega) a) := by
  obtain ⟨cs, h1, h2, hcr, p, hp, ε, hε, hneg⟩ := nested_genForm_neg hell3 hE hdvd hMe hM hR a
  refine ⟨cs, hcr, h1, fun hU α hα γ hγ => ?_⟩
  obtain ⟨t, htπ, hc1, hc2, hW⟩ := hU ε hε
  have hneg' := hneg t htπ hc1 hc2 hW.1.2.2 hW.1.2.1
  have hE0 : 0 ≤ bondEnergy (zfun (gU M R p) : AdalyFormal.Balaban.AdmissibleSubspace.Bond (neLu M R) → AdalyFormal.Balaban.CovariantOperators.SuTwo) :=
    AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _
  refine ⟨2, by norm_num, neLu M R, torusOK_ne hell3 hdvd hM, neS ell M R, ne_admissible hell3 hM hR, neLam M R,
    lambdaOK2_ne hell3 hdvd hM hR, stagU ell M R t, ne_stag_class hell3 hM hR t hα, hW, zfun (gU M R p),
    onLambdaTildeIn_gU hell3 hdvd hp, onLambdaT_gU hell3 hdvd hMe hp, ?_⟩
  exact lt_of_lt_of_le hneg' (mul_nonneg hγ.le hE0)

/-- **conditional refutation of the frozen headline `P428Target8NCWDH` along the staggered layer**: if for `ell` with `StagOK ell` (even, or odd `>= 3`: all `ell >= 3`), `3 <= ell`
(`3 <= ell`, `2 | ell`), some `a > 0`, infinitely many `m` and for each infinitely many `R`, the printed objects exist (`WellDefG`)
at parameters `t` with `cos t` arbitrarily close above the first crossing of the Z-chain form, then `P428Target8NCWDH` is false. -/
theorem not_WDH_of_nearUnits (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      ∃ cs : ℝ, IsCrossingN ell (ell ^ m) R cs ∧ NearUnits ell (ell ^ m) R (by omega) a cs) :
    FailEllC CfData.cf ell (by omega) a := by
  intro m₀
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, cs, hcs, hnu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hMe : ell + 3 ≤ ell ^ m := ell_add3_le_pow hell3 hm1
  refine ⟨R, le_trans (le_max_left _ _) hRR, ?_⟩
  obtain ⟨cs', hcs', _, hF⟩ := nested_stag_failAt hell3 hE hdvd hMe hM (le_trans (le_max_right _ _) hRR) a
  have := crossing_unique hcs hcs'
  subst this
  exact hF hnu

#print axioms nested_stag_failAt
#print axioms not_WDH_of_nearUnits

end AdalyFormal.CoverOmega
