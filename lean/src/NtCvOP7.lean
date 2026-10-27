import NtCvOP6
import NtCvOS12

/-!
# CvOP7 -- `gradL2`, `lapFull`, `lapDir`, `LmOf`, `Qlev`, `Bq` are analytic along an analytic regular tower (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- entries of the links analytic. -/
def LinkEA (U : ℝ → Cfg L) (t0 : ℝ) : Prop := ∀ b, EA (fun t => ((U t b : SU2) : M2)) t0

theorem LinkEA_of_AnaFam {U : ℝ → Cfg L} {t0 : ℝ} (h : AnaFam U t0) : LinkEA U t0 :=
  fun b => entAna_of_SGat (h b)

section Grad
variable {U : ℝ → Cfg L} {t0 : ℝ}

theorem gradL2_analytic (hU : LinkEA U t0) : AnalyticAt ℝ (fun t => gradL2 (U t)) t0 := by
  apply analyticAt_clm_of_apply
  intro f
  have hcoord : ∀ b : Bond L, AnalyticAt ℝ (fun t => RMap (U t b) (WithLp.ofLp f (periodicLatticeShift b.1 b.2)) - WithLp.ofLp f b.1) t0 :=
    fun b => (RMap_analytic (hU b) analyticAt_const).sub analyticAt_const
  have h := analyticAt_toLp (f := fun b t => RMap (U t b) (WithLp.ofLp f (periodicLatticeShift b.1 b.2)) - WithLp.ofLp f b.1) hcoord
  have e : (fun t => gradL2 (U t) f) = fun t => (WithLp.toLp 2 (fun b : Bond L =>
      RMap (U t b) (WithLp.ofLp f (periodicLatticeShift b.1 b.2)) - WithLp.ofLp f b.1) : BondFnL2 L) := by
    funext t
    exact WithLp.ofLp_injective 2 (gradL2_apply (U t) f)
  rw [e]; exact h

theorem gradAdj_analytic (hU : LinkEA U t0) : AnalyticAt ℝ (fun t => gradAdj (U t)) t0 :=
  anal_adjoint (gradL2_analytic hU)

theorem lapFull_analytic (hU : LinkEA U t0) : AnalyticAt ℝ (fun t => lapFull (U t)) t0 :=
  anal_comp (gradAdj_analytic hU) (gradL2_analytic hU)

theorem lapDir_analytic (G : TowerGeom L) (hU : LinkEA U t0) : AnalyticAt ℝ (fun t => lapDir G (U t)) t0 :=
  anal_comp (anal_comp analyticAt_const (lapFull_analytic hU)) analyticAt_const

theorem LmOf_analytic (G : TowerGeom L) (hU : LinkEA U t0) : AnalyticAt ℝ (fun t => LmOf G (U t)) t0 :=
  (lapDir_analytic G hU).add analyticAt_const

end Grad


end AdalyFormal.CoverOmega.Struct
