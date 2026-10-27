import NsCvOP12

/-!
# CvOP13 -- `deltaKLocCLM` and `Delta` are analytic in the link configuration (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2 (Cfg Delta TowerGeom)

variable {L : PeriodicLatticeExtent}

theorem analyticAt_inner_suTwo {u v : ℝ → SuTwo} {t0 : ℝ} (hu : AnalyticAt ℝ u t0) (hv : AnalyticAt ℝ v t0) :
    AnalyticAt ℝ (fun t => ⟪u t, v t⟫) t0 :=
  ((innerSL ℝ : SuTwo →L[ℝ] SuTwo →L[ℝ] ℝ).analyticAt_bilinear (u t0, v t0)).comp₂ hu hv

section D
variable {U : ℝ → Cfg L} {t0 : ℝ}

theorem deltaKLocCLM_analytic (hU : LinkEA U t0) (P : Set (PeriodicLatticePlaquette L)) :
    AnalyticAt ℝ (fun t => deltaKLocCLM (U t) P) t0 := by
  classical
  apply analyticAt_of_inner
  intro x y
  have e1 : ∀ t, (inner ℝ x (deltaKLocCLM (U t) P y) : ℝ)
      = (∑ p : PeriodicLatticePlaquette L, if p ∈ P then ⟪curlValueCovariant (U t) (WithLp.ofLp x) p, curlValueCovariant (U t) (WithLp.ofLp y) p⟫ else 0)
        + ((1 / 2 : ℝ) * ((1 / 2 : ℝ) * (deltaPrimeBilRawLoc (U t) P (WithLp.ofLp x) (WithLp.ofLp y)
            + deltaPrimeBilRawLoc (U t) P (WithLp.ofLp y) (WithLp.ofLp x)))) := by
    intro t
    rw [inner_deltaKLocCLM]
    congr 1
    · simp only [PiLp.inner_apply, plaqMask_apply]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      split_ifs
      · simp [curlCovariantLM_L2, curlCovariantLM]
        rfl
      · simp
  have e : (fun t => (inner ℝ x (deltaKLocCLM (U t) P y) : ℝ)) = _ := funext e1
  rw [e]
  refine AnalyticAt.add (Finset.analyticAt_fun_sum _ (fun p _ => ?_)) ?_
  · by_cases hp : p ∈ P
    · simp only [if_pos hp]
      exact analyticAt_inner_suTwo (curlValue_analytic hU _ p) (curlValue_analytic hU _ p)
    · simp only [if_neg hp]; exact analyticAt_const
  · have hraw : ∀ A B : Bond L → SuTwo, AnalyticAt ℝ (fun t => deltaPrimeBilRawLoc (U t) P A B) t0 := by
      intro A B
      simp only [deltaPrimeBilRawLoc_apply]
      refine Finset.analyticAt_fun_sum _ (fun p _ => ?_)
      by_cases hp : p ∈ P
      · simp only [if_pos hp]; exact bilPlaq_analytic hU p A B
      · simp only [if_neg hp]; exact analyticAt_const
    exact analyticAt_const.mul (analyticAt_const.mul ((hraw _ _).add (hraw _ _)))

theorem Delta_analytic (G : TowerGeom L) (hU : LinkEA U t0) :
    AnalyticAt ℝ (fun t => Delta G (U t)) t0 :=
  deltaKLocCLM_analytic hU _

end D

end AdalyFormal.CoverOmega.Struct
