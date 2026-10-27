import TL11c

/-!
# TL11d -- second derivative through a linear map
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped Topology

theorem fderiv2_comp_clm {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → F) (T : G →L[ℝ] E) (hf : ContDiffAt ℝ 2 f 0) (x y : G) :
    fderiv ℝ (fderiv ℝ (f ∘ T)) 0 x y = fderiv ℝ (fderiv ℝ f) 0 (T x) (T y) := by
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f z := by
    filter_upwards [hf.eventually (by simp)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hT : ∀ᶠ y in 𝓝 (0 : G), DifferentiableAt ℝ f (T y) := by
    have : Filter.Tendsto T (𝓝 (0 : G)) (𝓝 (0 : E)) := by
      have := T.continuous.tendsto (0 : G)
      rwa [map_zero] at this
    exact this.eventually hdiff
  have heq : fderiv ℝ (f ∘ T) =ᶠ[𝓝 0] fun y => (fderiv ℝ f (T y)).comp T := by
    filter_upwards [hT] with y hy
    rw [fderiv_comp y hy T.differentiableAt, T.fderiv]
  rw [heq.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set Φ : (E →L[ℝ] F) →L[ℝ] (G →L[ℝ] F) := (ContinuousLinearMap.compL ℝ G E F).flip T with hΦ
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (T 0) := by rw [map_zero]; exact hd2.hasFDerivAt
  have hB := hA.comp (0 : G) T.hasFDerivAt
  have hC := Φ.hasFDerivAt.comp (0 : G) hB
  have hfun : (fun y => (fderiv ℝ f (T y)).comp T) = Φ ∘ (fderiv ℝ f ∘ T) := by
    funext y; rfl
  rw [hfun]
  rw [hC.fderiv]
  rfl

end AdalyFormal.Thin
