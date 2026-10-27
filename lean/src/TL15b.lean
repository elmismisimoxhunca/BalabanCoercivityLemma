import TL15a

/-!
# TL15b -- `G`, `H`, the form `K`, `G₁⁻¹` (by uniqueness), `G₁`, `H₁` descend
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section hk
variable {Dd : Type} [Fintype Dd]
variable {H Ht : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Ht] [InnerProductSpace ℝ Ht] [FiniteDimensional ℝ Ht]

theorem HCov.inner_ell (c : HCov Dd H Ht) (x y : H) : ⟪c.ell x, c.ell y⟫ = (Fintype.card Dd : ℝ) * ⟪x, y⟫ := by
  have h := congrArg (fun T => ⟪T x, y⟫) c.adj_ell_ell
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_smul_left] at h
  simpa using h

theorem HCov.inner_rho (c : HCov Dd H Ht) (d : Dd) (x y : Ht) : ⟪c.rho d x, c.rho d y⟫ = ⟪x, y⟫ := by
  have h := congrArg (fun T => ⟪T x, y⟫) ((c.rho_orth d).2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  rw [ContinuousLinearMap.adjoint_inner_left] at h
  exact h

/-- descent: a deck-equivariant operator is `ℓ ∘ ((1/N) σ Õ ℓ)` on the periodic part -/
theorem he1_of_equi_descent [Nonempty Dd] (c : HCov Dd H Ht) (Ot : Ht →L[ℝ] Ht) (he : HEqui c c Ot) :
    HE1 c c ((1 / (Fintype.card Dd : ℝ)) • c.sig.comp (Ot.comp c.ell)) Ot := by
  have hN : (Fintype.card Dd : ℝ) ≠ 0 := by
    have : 0 < Fintype.card Dd := Fintype.card_pos
    positivity
  ext1 x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
  have hinv : ∀ d, c.rho d (Ot (c.ell x)) = Ot (c.ell x) := by
    intro d
    have := congrArg (fun T => T (c.ell x)) (he d)
    simp only [ContinuousLinearMap.comp_apply] at this
    have hρℓ : c.rho d (c.ell x) = c.ell x := congrArg (fun T => T x) (c.rho_ell d)
    rw [hρℓ] at this
    exact this.symm
  have hsum : c.ell (c.sig (Ot (c.ell x))) = (Fintype.card Dd : ℝ) • Ot (c.ell x) := by
    have := congrArg (fun T => T (Ot (c.ell x))) c.sum_rho
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, hinv, Finset.sum_const, Finset.card_univ] at this
    rw [HCov.sig, ← this]
    exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm
  rw [hsum, smul_smul, one_div, inv_mul_cancel₀ hN, one_smul]

end hk

section bd2
variable {Dd : Type} [Fintype Dd]
variable {E Et S St F Ft : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Et] [InnerProductSpace ℝ Et] [FiniteDimensional ℝ Et]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup St] [InnerProductSpace ℝ St] [FiniteDimensional ℝ St]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup Ft] [InnerProductSpace ℝ Ft] [FiniteDimensional ℝ Ft]
variable {D : BaseDataS E S F} {Dt : BaseDataS Et St Ft} {cE : HCov Dd E Et} {cS : HCov Dd S St} {cF : HCov Dd F Ft}

theorem BDLink.G [Nonempty Dd] (hl : BDLink (Dd := Dd) D Dt cE cS cF) (hu : IsUnit Dt.Ginv) :
    IsUnit D.Ginv ∧ HDesc cE cE D.G Dt.G := hl.ginv.inverse hu

theorem BDLink.H [Nonempty Dd] (hl : BDLink (Dd := Dd) D Dt cE cS cF) (hu : IsUnit Dt.Ginv)
    (hM : IsUnit ((Dt.Q.comp Dt.G).comp Dt.Qs)) : HDesc cF cE D.H Dt.H := by
  have hG := (hl.G hu).2
  have hM' : HDesc cF cF ((D.Q.comp D.G).comp D.Qs) ((Dt.Q.comp Dt.G).comp Dt.Qs) := (hl.qs.comp hG).comp hl.q
  unfold BaseDataS.H
  exact ((hM'.inverse hM).2.comp hl.qs).comp hG

theorem BDLink.K_ell (hl : BDLink (Dd := Dd) D Dt cE cS cF) (hH : HDesc cF cE D.H Dt.H) (A : E) :
    Dt.K (cE.ell A) = (Fintype.card Dd : ℝ) * D.K A := by
  have e1 : Dt.Dpi (cE.ell A) = cE.ell (D.Dpi A) := congrArg (fun T => T A) hl.dpi.e1
  have e2 : Dt.Mass (cE.ell A) = cE.ell (D.Mass A) := congrArg (fun T => T A) hl.mass.e1
  have e3 : Dt.T (cE.ell A) = cS.ell (D.T A) := congrArg (fun T => T A) hl.t.e1
  have e4 : Dt.H (cF.ell (D.C2 A)) = cE.ell (D.H (D.C2 A)) := congrArg (fun T => T (D.C2 A)) hH.e1
  unfold BaseDataS.K
  rw [e1, e2, e3, hl.c2_ell, e4, hl.j, HCov.inner_ell, HCov.inner_ell, HCov.inner_ell,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, HCov.inner_ell]
  ring

theorem BDLink.K_rho (hl : BDLink (Dd := Dd) D Dt cE cS cF) (hH : HDesc cF cE D.H Dt.H) (d : Dd) (A : Et) :
    Dt.K (cE.rho d A) = Dt.K A := by
  have e1 : Dt.Dpi (cE.rho d A) = cE.rho d (Dt.Dpi A) := congrArg (fun T => T A) (hl.dpi.equi d)
  have e2 : Dt.Mass (cE.rho d A) = cE.rho d (Dt.Mass A) := congrArg (fun T => T A) (hl.mass.equi d)
  have e3 : Dt.T (cE.rho d A) = cS.rho d (Dt.T A) := congrArg (fun T => T A) (hl.t.equi d)
  have e4 : Dt.H (cF.rho d (Dt.C2 A)) = cE.rho d (Dt.H (Dt.C2 A)) := congrArg (fun T => T (Dt.C2 A)) (hH.equi d)
  have hJ : cE.rho d Dt.J = Dt.J := by rw [hl.j]; exact congrArg (fun T => T (D.J)) (cE.rho_ell d)
  unfold BaseDataS.K
  rw [e1, e2, e3, hl.c2_rho, e4]
  conv_lhs => rw [← hJ]
  simp only [← real_inner_self_eq_norm_sq, HCov.inner_rho]

/-- `G₁⁻¹` descends, by uniqueness of the symmetric operator with the printed form -/
theorem BDLink.G1inv [Nonempty Dd] (hl : BDLink (Dd := Dd) D Dt cE cS cF) (hH : HDesc cF cE D.H Dt.H)
    {X : E →L[ℝ] E} (hX : D.IsG1inv X) {Xt : Et →L[ℝ] Et} (hXt : Dt.IsG1inv Xt) : HDesc cE cE X Xt := by
  have hN : (Fintype.card Dd : ℝ) ≠ 0 := by
    have : 0 < Fintype.card Dd := Fintype.card_pos
    positivity
  have hequi : HEqui cE cE Xt := by
    intro d
    obtain ⟨hP, hPs⟩ := cE.rho_orth d
    have hsym : ∀ x y, ⟪(ContinuousLinearMap.adjoint (cE.rho d)).comp (Xt.comp (cE.rho d)) x, y⟫ =
        ⟪x, (ContinuousLinearMap.adjoint (cE.rho d)).comp (Xt.comp (cE.rho d)) y⟫ := by
      intro x y
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
      exact hXt.symm _ _
    have hform : ∀ A, ⟪A, ((ContinuousLinearMap.adjoint (cE.rho d)).comp (Xt.comp (cE.rho d))) A⟫ = ⟪A, Xt A⟫ := by
      intro A
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rw [hXt.form, hXt.form]
      exact hl.K_rho hH d A
    have heq := symm_unique hsym hXt.symm hform
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    have := congrArg (fun T => cE.rho d (T x)) heq
    simp only [ContinuousLinearMap.comp_apply] at this
    have e : cE.rho d (ContinuousLinearMap.adjoint (cE.rho d) (Xt (cE.rho d x))) = Xt (cE.rho d x) :=
      congrArg (fun T => T (Xt (cE.rho d x))) hP
    rw [e] at this
    exact this
  have he1 := he1_of_equi_descent cE Xt hequi
  set O : E →L[ℝ] E := (1 / (Fintype.card Dd : ℝ)) • cE.sig.comp (Xt.comp cE.ell) with hO
  have hOsym : ∀ x y, ⟪O x, y⟫ = ⟪x, O y⟫ := by
    intro x y
    simp only [hO, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right, HCov.sig,
      ContinuousLinearMap.adjoint_inner_left]
    rw [hXt.symm (cE.ell x) (cE.ell y)]
    simp [ContinuousLinearMap.adjoint_inner_right]
  have hOform : ∀ A, ⟪A, O A⟫ = D.K A := by
    intro A
    simp only [hO, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_right, HCov.sig,
      ContinuousLinearMap.adjoint_inner_right]
    rw [hXt.form, hl.K_ell hH A]
    field_simp
  have hOX : O = X := symm_unique hOsym hX.symm (fun A => by rw [hOform, hX.form])
  rw [hOX] at he1
  exact hdesc_of_he1_equi he1 hequi

end bd2

end AdalyFormal.Thin
