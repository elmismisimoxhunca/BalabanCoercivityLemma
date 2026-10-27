import NtCvOP2
import ZXR2Sector

/-!
# CvOP3 -- the one-step and composite jets are analytic in the background parameter (lane omega/near2/struct)

`QlinStepL`, `D2StepL` (r8 local jets, per-component Frechet derivatives of the coordinate one-step map) along an analytic
family of regular backgrounds `V t`; composite `QlinCompL`, `D2CompL` along a tower `bg t j`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega (RegBg2)

variable {L : PeriodicLatticeExtent}

theorem SGat_comp_fst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {t0 : ℝ} {W : ℝ → SU2}
    (h : SGat t0 W) (y : F) : SGat ((t0, y) : ℝ × F) (fun e => W e.1) := by
  have h' : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) t0 := h
  exact ContDiffAt.comp (g := fun t => ((W t : SU2) : M2)) (f := Prod.fst) ((t0, y)) h' contDiffAt_fst

/-- a family of configurations analytic in the parameter. -/
def AnaFam (V : ℝ → PeriodicLinkConfiguration SU2 L) (t0 : ℝ) : Prop :=
  ∀ b, SGat t0 (fun t => V t b)

section Step
variable (s ell : ℕ) (V : ℝ → PeriodicLinkConfiguration SU2 L) {t0 : ℝ}

theorem F_contDiff (hV : AnaFam V t0) (hreg : RegBg2 s ell (V t0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × XS L => qStepX s ell (V p.1) p.2 c) (t0, 0) := by
  have hV' : ∀ b, SGat ((t0, (0 : XS L)) : ℝ × XS L) (fun e : ℝ × XS L => V e.1 b) := fun b => SGat_comp_fst (hV b) 0
  exact qStepX_param (e0 := ((t0, (0 : XS L)) : ℝ × XS L)) s ell (fun e : ℝ × XS L => V e.1) (fun e => e.2)
    hV' contDiffAt_snd rfl hreg c

theorem QlinStepL_analytic (hV : AnaFam V t0) (hreg : RegBg2 s ell (V t0)) :
    AnalyticAt ℝ (fun t => QlinStepL s ell (V t)) t0 := by
  apply analyticAt_clm_of_apply
  intro a
  refine analyticAt_pi_iff.2 (fun c => ?_)
  have h := (cd_partial1 (F_contDiff s ell V hV hreg c)).analyticAt
  have := anal_apply h (analyticAt_const (v := a))
  exact this

theorem QlinStepL_apply_analytic (hV : AnaFam V t0) (hreg : RegBg2 s ell (V t0)) {u : ℝ → XS L}
    (hu : AnalyticAt ℝ u t0) : AnalyticAt ℝ (fun t => QlinStepL s ell (V t) (u t)) t0 :=
  anal_apply (QlinStepL_analytic s ell V hV hreg) hu

theorem D2StepL_analytic (hV : AnaFam V t0) (hreg : RegBg2 s ell (V t0)) {u v : ℝ → XS L}
    (hu : AnalyticAt ℝ u t0) (hv : AnalyticAt ℝ v t0) :
    AnalyticAt ℝ (fun t => D2StepL s ell (V t) (u t) (v t)) t0 := by
  refine analyticAt_pi_iff.2 (fun c => ?_)
  have h := (cd_partial2 (F_contDiff s ell V hV hreg c)).analyticAt
  have h1 := anal_apply (anal_apply h hu) hv
  exact h1

end Step

section Tower
variable (ell : ℕ) (bg : ℝ → ℕ → PeriodicLinkConfiguration SU2 L) {t0 : ℝ} (J : ℕ)

theorem QlinCompL_analytic (hbg : ∀ j, j < J → AnaFam (fun t => bg t j) t0)
    (hreg : ∀ j, j < J → RegBg2 (ell ^ j) ell (bg t0 j)) :
    ∀ j, j ≤ J → AnalyticAt ℝ (fun t => QlinCompL ell (bg t) j) t0 := by
  intro j
  induction j with
  | zero => intro _; exact analyticAt_const
  | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := QlinStepL_analytic (ell ^ j) ell (fun t => bg t j) (hbg j (by omega)) (hreg j (by omega))
      exact anal_comp h2 h1

theorem D2CompL_analytic (hbg : ∀ j, j < J → AnaFam (fun t => bg t j) t0)
    (hreg : ∀ j, j < J → RegBg2 (ell ^ j) ell (bg t0 j)) {u v : ℝ → XS L}
    (hu : AnalyticAt ℝ u t0) (hv : AnalyticAt ℝ v t0) :
    ∀ j, j ≤ J → AnalyticAt ℝ (fun t => D2CompL ell (bg t) j (u t) (v t)) t0 := by
  intro j
  induction j with
  | zero => intro _; simp only [D2CompL, LinearMap.zero_apply]; exact analyticAt_const
  | succ j ih =>
      intro hj
      have hq := QlinCompL_analytic ell bg J hbg hreg j (by omega)
      have h1 := ih (by omega)
      have h2 := QlinStepL_apply_analytic (ell ^ j) ell (fun t => bg t j) (hbg j (by omega)) (hreg j (by omega)) h1
      have h3 := D2StepL_analytic (ell ^ j) ell (fun t => bg t j) (hbg j (by omega)) (hreg j (by omega))
        (anal_apply hq hu) (anal_apply hq hv)
      simp only [D2CompL, LinearMap.mk₂_apply]
      exact h2.add h3

end Tower

end AdalyFormal.CoverOmega.Struct
