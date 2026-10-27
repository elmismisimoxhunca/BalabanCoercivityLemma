import NsCvOS1

/-!
# CvOS2 -- analyticity infrastructure for CLM-valued families (lane omega/near2/struct)

`analyticAt_cdet`, `analyticAt_cadj`: `cdet`/`cadj` of an analytic family of endomorphisms are analytic (polynomial in the entries).
`anal_comp`, `anal_apply`, `adjL`: composition, application, adjoint of analytic families.
`flipL`: `Cb ↦ Cb.flip` as a continuous linear map.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open Matrix

section Det
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem analyticAt_det {n : Type*} [Fintype n] [DecidableEq n] {M : ℝ → Matrix n n ℝ} {t0 : ℝ}
    (hM : ∀ i j, AnalyticAt ℝ (fun t => M t i j) t0) : AnalyticAt ℝ (fun t => (M t).det) t0 := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ (fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hM _ _)))

theorem analyticAt_adjugate_entry {n : Type*} [Fintype n] [DecidableEq n] {M : ℝ → Matrix n n ℝ} {t0 : ℝ}
    (hM : ∀ i j, AnalyticAt ℝ (fun t => M t i j) t0) (i j : n) :
    AnalyticAt ℝ (fun t => (M t).adjugate i j) t0 := by
  simp only [Matrix.adjugate_apply]
  apply analyticAt_det
  intro r c
  by_cases h : r = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne h]
    exact hM r c

theorem analyticAt_mat_entry {f : ℝ → X →L[ℝ] X} {t0 : ℝ} (hf : AnalyticAt ℝ f t0)
    (i j : Fin (Module.finrank ℝ X)) : AnalyticAt ℝ (fun t => mat (f t) i j) t0 := by
  simp only [mat_apply]
  exact ((entL X i j).analyticAt (f t0)).comp hf

theorem analyticAt_cdet {f : ℝ → X →L[ℝ] X} {t0 : ℝ} (hf : AnalyticAt ℝ f t0) :
    AnalyticAt ℝ (fun t => cdet (f t)) t0 := by
  simp only [cdet_eq]
  exact analyticAt_det (fun i j => analyticAt_mat_entry hf i j)

theorem analyticAt_cadj {f : ℝ → X →L[ℝ] X} {t0 : ℝ} (hf : AnalyticAt ℝ f t0) :
    AnalyticAt ℝ (fun t => cadj (f t)) t0 := by
  simp only [cadj]
  refine Finset.analyticAt_fun_sum _ (fun i _ => Finset.analyticAt_fun_sum _ (fun j _ => ?_))
  exact (analyticAt_adjugate_entry (fun i j => analyticAt_mat_entry hf i j) i j).smul analyticAt_const

end Det

section Ops
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem anal_comp {g : ℝ → F →L[ℝ] G} {f : ℝ → E →L[ℝ] F} {t0 : ℝ}
    (hg : AnalyticAt ℝ g t0) (hf : AnalyticAt ℝ f t0) : AnalyticAt ℝ (fun t => (g t).comp (f t)) t0 :=
  ((ContinuousLinearMap.compL ℝ E F G).analyticAt_bilinear (g t0, f t0)).comp₂ hg hf

theorem anal_apply {g : ℝ → E →L[ℝ] F} {v : ℝ → E} {t0 : ℝ}
    (hg : AnalyticAt ℝ g t0) (hv : AnalyticAt ℝ v t0) : AnalyticAt ℝ (fun t => (g t) (v t)) t0 :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (g t0, v t0)).comp₂ hg hv

end Ops

section Adj
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- the adjoint as a continuous real-linear map. -/
noncomputable def adjL (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => by
        have := map_smulₛₗ (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)) c A
        simpa using this }

theorem adjL_apply (A : E →L[ℝ] F) : adjL E F A = ContinuousLinearMap.adjoint A := rfl

theorem anal_adjoint {f : ℝ → E →L[ℝ] F} {t0 : ℝ} (hf : AnalyticAt ℝ f t0) :
    AnalyticAt ℝ (fun t => ContinuousLinearMap.adjoint (f t)) t0 :=
  ((adjL E F).analyticAt (f t0)).comp hf

end Adj

end AdalyFormal.CoverOmega.Struct
