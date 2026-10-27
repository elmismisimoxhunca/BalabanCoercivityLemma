
namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open Filter Set

section T
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- T1: abstract, DifferentiableAt → HasDerivAt
theorem pt1 (f : ℝ → E →L[ℝ] E) (x : ℝ) (h : DifferentiableAt ℝ f x) : HasDerivAt f (deriv f x) x :=
  h.hasDerivAt

-- T3: abstract, ContDiff → HasDerivAt
theorem pt3 (f : ℝ → E →L[ℝ] E) (hf : ContDiff ℝ ⊤ f) (x : ℝ) : ∃ f', HasDerivAt f f' x :=
  ⟨_, ((hf.differentiable (by simp)) x).hasDerivAt⟩

-- T4: instance equality by rfl
theorem pt4 : (NormedAddCommGroup.toAddCommGroup : AddCommGroup (E →L[ℝ] E)) = ContinuousLinearMap.addCommGroup := rfl

-- T5: abstract chain, normed world, then const_add
theorem pt5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (M : ℝ → H →L[ℝ] H) (hM : ContDiff ℝ ⊤ M) (P : H →L[ℝ] E) (I : E →L[ℝ] H) (A : E →L[ℝ] E) (t₀ : ℝ) :
    ∃ X' : E →L[ℝ] E, HasDerivAt (fun t => A + P.comp ((M t).comp I)) X' t₀ := by
  have hd : Differentiable ℝ (fun t => A + P.comp ((M t).comp I)) := by
    have h1 := (differentiable_const P).clm_comp ((hM.differentiable (by simp)).clm_comp (differentiable_const I))
    exact (differentiable_const A).add h1
  exact ⟨_, (hd t₀).hasDerivAt⟩
end T

end AdalyFormal.Round9.Guarded.AnalyticR2
