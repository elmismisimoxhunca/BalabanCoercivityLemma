import NsCvOP1

/-!
# CvOP2 -- analytic dependence on the parameter of the partial Frechet derivatives and of the one-step jets (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology

section Gen
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace Y]

/-- the partial Frechet derivative in the second variable of a jointly analytic function is jointly analytic. -/
theorem cd_partial {F : ℝ × X → Y} {p0 : ℝ × X} (hF : ContDiffAt ℝ ⊤ F p0) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × X => fderiv ℝ (fun a => F (p.1, a)) p.2) p0 := by
  have hev : ∀ᶠ p in 𝓝 p0, ContDiffAt ℝ ⊤ F p := hF.eventually (by simp)
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ F) p0 := hF.fderiv_right (m := ⊤) (by simp)
  have hc : ContDiffAt ℝ ⊤ (fun p => (ContinuousLinearMap.precomp Y (ContinuousLinearMap.inr ℝ ℝ X)) (fderiv ℝ F p)) p0 :=
    (ContinuousLinearMap.contDiff _).contDiffAt.comp p0 hd
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have h1 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) := (hp.differentiableAt (by simp)).hasFDerivAt
  have h2 := h1.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
  exact h2.fderiv

/-- second partial derivative at `a = 0`, as a function of the parameter. -/
theorem cd_partial2 {F : ℝ × X → Y} {t0 : ℝ} (hF : ContDiffAt ℝ ⊤ F (t0, 0)) :
    ContDiffAt ℝ ⊤ (fun t : ℝ => fderiv ℝ (fderiv ℝ (fun a => F (t, a))) 0) t0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun p : ℝ × X => fderiv ℝ (fun a => F (p.1, a)) p.2) (t0, 0) := cd_partial hF
  have h2 : ContDiffAt ℝ ⊤ (fun p : ℝ × X =>
      fderiv ℝ (fun a => fderiv ℝ (fun a' => F (p.1, a')) a) p.2) (t0, 0) :=
    cd_partial (F := fun p : ℝ × X => fderiv ℝ (fun a => F (p.1, a)) p.2) h1
  have h3 : ContDiffAt ℝ ⊤ (fun t : ℝ => (fun p : ℝ × X =>
      fderiv ℝ (fun a => fderiv ℝ (fun a' => F (p.1, a')) a) p.2) (t, 0)) t0 :=
    h2.comp t0 (contDiffAt_id.prodMk contDiffAt_const)
  exact h3

theorem cd_partial1 {F : ℝ × X → Y} {t0 : ℝ} (hF : ContDiffAt ℝ ⊤ F (t0, 0)) :
    ContDiffAt ℝ ⊤ (fun t : ℝ => fderiv ℝ (fun a => F (t, a)) 0) t0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun p : ℝ × X => fderiv ℝ (fun a => F (p.1, a)) p.2) (t0, 0) := cd_partial hF
  exact h1.comp t0 (contDiffAt_id.prodMk contDiffAt_const)

end Gen

section ClmApply
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- a family of continuous linear maps out of a finite-dimensional space is analytic iff it is pointwise. -/
theorem analyticAt_clm_of_apply (T : ℝ → X →L[ℝ] Y) {t0 : ℝ}
    (h : ∀ x, AnalyticAt ℝ (fun t => T t x) t0) : AnalyticAt ℝ T t0 := by
  let b := Module.finBasis ℝ X
  have hT : ∀ t, T t = ∑ j, (ContinuousLinearMap.smulRightL ℝ X Y (LinearMap.toContinuousLinearMap (b.coord j))) (T t (b j)) := by
    intro t
    ext1 x
    have e : ∀ j, (ContinuousLinearMap.smulRightL ℝ X Y (LinearMap.toContinuousLinearMap (b.coord j))) (T t (b j)) x
        = (b.coord j x) • T t (b j) := fun j => rfl
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, e]
    have hx : T t x = T t (∑ j, b.repr x j • b j) := by rw [b.sum_repr x]
    rw [hx, map_sum]
    simp [map_smul]
  have : T = fun t => ∑ j, (ContinuousLinearMap.smulRightL ℝ X Y (LinearMap.toContinuousLinearMap (b.coord j))) (T t (b j)) :=
    funext hT
  rw [this]
  exact Finset.analyticAt_fun_sum _ (fun j _ => ((ContinuousLinearMap.smulRightL ℝ X Y _).analyticAt _).comp (h (b j)))

end ClmApply

end AdalyFormal.CoverOmega.Struct
