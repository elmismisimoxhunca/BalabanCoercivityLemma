import TL13c

/-!
# TL13d -- restriction of an abstract cover to invariant subspaces
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section restr
variable {D : Type} [Fintype D]
variable {H Ht : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Ht] [InnerProductSpace ℝ Ht] [FiniteDimensional ℝ Ht]

/-- restrict a continuous linear map between ambient spaces to subspaces -/
noncomputable def restrictCLM {V : Submodule ℝ H} {Vt : Submodule ℝ Ht} (A : H →L[ℝ] Ht) (hA : ∀ x ∈ V, A x ∈ Vt) : V →L[ℝ] Vt :=
  (A.comp V.subtypeL).codRestrict Vt (fun x => hA x.1 x.2)

theorem restrictCLM_coe {V : Submodule ℝ H} {Vt : Submodule ℝ Ht} (A : H →L[ℝ] Ht) (hA : ∀ x ∈ V, A x ∈ Vt) (x : V) :
    ((restrictCLM A hA x : Vt) : Ht) = A x := rfl

theorem adjoint_restrictCLM {V : Submodule ℝ H} {Vt : Submodule ℝ Ht} (A : H →L[ℝ] Ht) (B : Ht →L[ℝ] H)
    (hA : ∀ x ∈ V, A x ∈ Vt) (hB : ∀ y ∈ Vt, B y ∈ V) (hAB : ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) :
    ContinuousLinearMap.adjoint (restrictCLM A hA) = restrictCLM B hB := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  have := hAB x.1 y.1
  simp only [Submodule.coe_inner, restrictCLM_coe]
  calc ⟪B y.1, x.1⟫ = ⟪x.1, B y.1⟫ := (real_inner_comm _ _).symm
    _ = ⟪A x.1, y.1⟫ := this.symm
    _ = ⟪y.1, A x.1⟫ := (real_inner_comm _ _).symm

theorem restrictCLM_comp {V : Submodule ℝ H} {Vt : Submodule ℝ Ht} {W : Submodule ℝ H} {Wt : Submodule ℝ Ht}
    {A : H →L[ℝ] Ht} {B : Ht →L[ℝ] Ht} (hA : ∀ x ∈ V, A x ∈ Vt) (hB : ∀ y ∈ Vt, B y ∈ Wt) (hBA : ∀ x ∈ V, B (A x) ∈ Wt) :
    (restrictCLM B hB).comp (restrictCLM A hA) = restrictCLM (B.comp A) hBA := by
  ext1 x; rfl

/-- restrict an abstract cover to subspaces -/
noncomputable def HCov.restrict (c : HCov D H Ht) (V : Submodule ℝ H) (Vt : Submodule ℝ Ht)
    (hℓ : ∀ x ∈ V, c.ell x ∈ Vt) (hρ : ∀ d, ∀ y ∈ Vt, c.rho d y ∈ Vt)
    (hρa : ∀ d, ∀ y ∈ Vt, ContinuousLinearMap.adjoint (c.rho d) y ∈ Vt) (hσ : ∀ y ∈ Vt, c.sig y ∈ V) : HCov D V Vt where
  ell := restrictCLM c.ell hℓ
  rho := fun d => restrictCLM (c.rho d) (hρ d)
  rho_ell := fun d => by
    ext1 x
    exact Subtype.ext (congrArg (fun T => T x.1) (c.rho_ell d))
  sum_rho := by
    have hadj : ContinuousLinearMap.adjoint (restrictCLM c.ell hℓ : V →L[ℝ] Vt) = restrictCLM c.sig hσ :=
      adjoint_restrictCLM c.ell c.sig hℓ hσ (fun x y => by
        simp only [HCov.sig]; rw [ContinuousLinearMap.adjoint_inner_right])
    rw [hadj]
    ext1 y
    apply Subtype.ext
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, restrictCLM_coe]
    have := congrArg (fun T => T y.1) c.sum_rho
    simpa [ContinuousLinearMap.sum_apply, HCov.sig, restrictCLM_coe] using this
  adj_ell_ell := by
    have hadj : ContinuousLinearMap.adjoint (restrictCLM c.ell hℓ : V →L[ℝ] Vt) = restrictCLM c.sig hσ :=
      adjoint_restrictCLM c.ell c.sig hℓ hσ (fun x y => by
        simp only [HCov.sig]; rw [ContinuousLinearMap.adjoint_inner_right])
    rw [hadj]
    ext1 x
    apply Subtype.ext
    simp only [ContinuousLinearMap.comp_apply, restrictCLM_coe, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    have := congrArg (fun T => T x.1) c.adj_ell_ell
    simpa [HCov.sig] using this
  rho_orth := fun d => by
    have hadj : ContinuousLinearMap.adjoint (restrictCLM (c.rho d) (hρ d) : Vt →L[ℝ] Vt) =
        restrictCLM (ContinuousLinearMap.adjoint (c.rho d)) (hρa d) :=
      adjoint_restrictCLM (c.rho d) (ContinuousLinearMap.adjoint (c.rho d)) (hρ d) (hρa d) (fun x y => by
        rw [ContinuousLinearMap.adjoint_inner_right])
    rw [hadj]
    constructor
    · ext1 y
      apply Subtype.ext
      simp only [ContinuousLinearMap.comp_apply, restrictCLM_coe, ContinuousLinearMap.id_apply]
      exact congrArg (fun T => T y.1) (c.rho_orth d).1
    · ext1 y
      apply Subtype.ext
      simp only [ContinuousLinearMap.comp_apply, restrictCLM_coe, ContinuousLinearMap.id_apply]
      exact congrArg (fun T => T y.1) (c.rho_orth d).2

theorem HCov.restrict_sig (c : HCov D H Ht) (V : Submodule ℝ H) (Vt : Submodule ℝ Ht)
    (hℓ : ∀ x ∈ V, c.ell x ∈ Vt) (hρ : ∀ d, ∀ y ∈ Vt, c.rho d y ∈ Vt)
    (hρa : ∀ d, ∀ y ∈ Vt, ContinuousLinearMap.adjoint (c.rho d) y ∈ Vt) (hσ : ∀ y ∈ Vt, c.sig y ∈ V) :
    (c.restrict V Vt hℓ hρ hρa hσ).sig = restrictCLM c.sig hσ :=
  adjoint_restrictCLM c.ell c.sig hℓ hσ (fun x y => by simp only [HCov.sig]; rw [ContinuousLinearMap.adjoint_inner_right])

end restr



end AdalyFormal.Thin
