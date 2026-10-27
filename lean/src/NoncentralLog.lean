import SmallBackground
import LocalLog
set_option autoImplicit false
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HConstruction.SmallNF
open AdalyFormal.Balaban.SuTwoLogExp
open AdalySI1.RawUbarDerivNoLoop (Yof_eq_ambient su2Log_eq_kappa_rsmul)
open AdalyFormal.Balaban.RegularityGap (Yof)

/-- Explicit local principal-log guard includes the removable identity point. -/
def LogGuard (g : SU2) : Prop := g = 1 ∨
  (-1 < (Matrix.trace (g : M2)).re / 2 ∧ (Matrix.trace (g : M2)).re / 2 < 1)

theorem logGuard_ne_cut (g : SU2) (hg : LogGuard g) : g ≠ su2NegOne := by
  rcases hg with hg | hg
  · rw [hg]; exact su2NegOne_ne_one.symm
  · intro h
    simp [h,coe_su2NegOne,Matrix.trace_neg] at hg

theorem log_smooth_guard {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → SU2} {x : E}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x) (hg : LogGuard (V x)) :
    ContDiffAt ℝ ⊤ (fun t => su2Log (V t)) x := by
  rcases hg with h1 | ⟨hlo,hhi⟩
  · exact HConstruction.LocalLog.contDiffAt_log_at_one hV h1
  let tr : M2 →ₗ[ℝ] ℝ := Complex.reLm.comp
    ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).restrictScalars ℝ)
  have htr : ContDiffAt ℝ ⊤ (fun t => (Matrix.trace ((V t : SU2) : M2)).re / 2) x :=
    (tr.toContinuousLinearMap.contDiff.contDiffAt.comp x hV).div_const 2
  have ha : ContDiffAt ℝ ⊤ (fun t => su2Angle (V t)) x :=
    (Real.contDiffAt_arccos (ne_of_gt hlo) (ne_of_lt hhi)).comp x htr
  have hn : Real.sin (su2Angle (V x)) ≠ 0 := by
    rw [su2Angle,Real.sin_arccos]
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    nlinarith
  have hk : ContDiffAt ℝ ⊤ (fun t => su2Kappa (V t)) x := ha.div ha.sin hn
  have hy : ContDiffAt ℝ ⊤ (fun t => Yof (V t)) x := by
    have he : (fun t => Yof (V t)) = fun t => ((V t : SU2) : M2) -
        ((Matrix.trace ((V t : SU2) : M2)).re / 2 : ℝ) • (1 : M2) := by
      funext t
      rw [Yof_eq_ambient]
      rfl
    rw [he]
    exact hV.sub (htr.smul contDiffAt_const)
  have hh := hk.smul hy
  convert hh using 1
  funext t
  exact su2Log_eq_kappa_rsmul (V t)
end HConstruction.SmallNF
