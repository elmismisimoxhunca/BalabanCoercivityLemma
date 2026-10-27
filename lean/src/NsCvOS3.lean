import NsCvOS2
import R2Algebra

/-!
# CvOS3 -- the core determinant `Dcore` (lane omega/near2/struct)

For core data `(A, Q, Cb, J)` (`A = Ginv`, `Q`, symmetric bilinear `Cb` with `C2 x = Cb x x`, source `J`):
`Mc = Q adj(A) Q*`, `Hh = adj(A) Q* adj(Mc)`, `Kh = Hh* J`, `Bt = det(Mc) A - 2 Lam(Cb, Kh)`, `Nh = Q adj(Bt) Q*`,
`Dcore = det A * det Mc * det Bt * det Nh`: a polynomial in the entries of `(A, Q, Cb, J)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace

section Core
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Cb ↦ Cb.flip` as a continuous linear map. -/
noncomputable def flipL (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    (E →L[ℝ] E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Cb => Cb.flip
      map_add' := fun A B => by ext x y; simp
      map_smul' := fun c A => by ext x y; simp }

theorem flipL_apply (Cb : E →L[ℝ] E →L[ℝ] F) (x y : E) : flipL E F Cb x y = Cb y x := rfl

/-- `Lam(Cb, κ) y = (Cb(·, y))* κ`, i.e. `⟪x, Lam y⟫ = ⟪Cb x y, κ⟫`. -/
noncomputable def lam0 (Cb : E →L[ℝ] E →L[ℝ] F) (κ : F) : E →L[ℝ] E :=
  ((ContinuousLinearMap.apply ℝ E κ).comp (adjL E F)).comp (flipL E F Cb)

theorem lam0_apply (Cb : E →L[ℝ] E →L[ℝ] F) (κ : F) (y : E) :
    lam0 Cb κ y = ContinuousLinearMap.adjoint (flipL E F Cb y) κ := rfl

theorem inner_lam0 (Cb : E →L[ℝ] E →L[ℝ] F) (κ : F) (x y : E) : ⟪x, lam0 Cb κ y⟫ = ⟪Cb x y, κ⟫ := by
  rw [lam0_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- bilinear packaging of `lam0`. -/
noncomputable def lamB : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Cb => LinearMap.toContinuousLinearMap
        { toFun := fun κ => lam0 Cb κ
          map_add' := fun a b => by ext y; simp [lam0_apply]
          map_smul' := fun c a => by ext y; simp [lam0_apply] }
      map_add' := fun A B => by
        ext κ y
        simp [lam0_apply]
      map_smul' := fun c A => by
        ext κ y
        simp [lam0_apply] }

theorem lamB_apply (Cb : E →L[ℝ] E →L[ℝ] F) (κ : F) : lamB Cb κ = lam0 Cb κ := rfl

theorem analyticAt_lam {Cb : ℝ → E →L[ℝ] E →L[ℝ] F} {κ : ℝ → F} {t0 : ℝ}
    (hC : AnalyticAt ℝ Cb t0) (hκ : AnalyticAt ℝ κ t0) : AnalyticAt ℝ (fun t => lamB (Cb t) (κ t)) t0 :=
  ((lamB (E := E) (F := F)).analyticAt_bilinear (Cb t0, κ t0)).comp₂ hC hκ

/-- `Mc = Q adj(A) Q*`. -/
noncomputable def Mc (A : E →L[ℝ] E) (Q : E →L[ℝ] F) : F →L[ℝ] F :=
  (Q.comp (cadj A)).comp (ContinuousLinearMap.adjoint Q)

/-- `Hh = adj(A) Q* adj(Mc)`. -/
noncomputable def Hh (A : E →L[ℝ] E) (Q : E →L[ℝ] F) : F →L[ℝ] E :=
  ((cadj A).comp (ContinuousLinearMap.adjoint Q)).comp (cadj (Mc A Q))

noncomputable def Kh (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (J : E) : F := ContinuousLinearMap.adjoint (Hh A Q) J

/-- `Bt = det(Mc) A - 2 Lam(Cb, Kh)`. -/
noncomputable def Bt (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (Cb : E →L[ℝ] E →L[ℝ] F) (J : E) : E →L[ℝ] E :=
  cdet (Mc A Q) • A - (2 : ℝ) • lamB Cb (Kh A Q J)

noncomputable def Nh (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (Cb : E →L[ℝ] E →L[ℝ] F) (J : E) : F →L[ℝ] F :=
  (Q.comp (cadj (Bt A Q Cb J))).comp (ContinuousLinearMap.adjoint Q)

/-- THE CORE DETERMINANT. -/
noncomputable def Dcore (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (Cb : E →L[ℝ] E →L[ℝ] F) (J : E) : ℝ :=
  cdet A * cdet (Mc A Q) * cdet (Bt A Q Cb J) * cdet (Nh A Q Cb J)

section Ana
variable {A : ℝ → E →L[ℝ] E} {Q : ℝ → E →L[ℝ] F} {Cb : ℝ → E →L[ℝ] E →L[ℝ] F} {J : ℝ → E} {t0 : ℝ}

theorem analyticAt_Mc (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) :
    AnalyticAt ℝ (fun t => Mc (A t) (Q t)) t0 :=
  anal_comp (anal_comp hQ (analyticAt_cadj hA)) (anal_adjoint hQ)

theorem analyticAt_Hh (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) :
    AnalyticAt ℝ (fun t => Hh (A t) (Q t)) t0 :=
  anal_comp (anal_comp (analyticAt_cadj hA) (anal_adjoint hQ)) (analyticAt_cadj (analyticAt_Mc hA hQ))

theorem analyticAt_Kh (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) (hJ : AnalyticAt ℝ J t0) :
    AnalyticAt ℝ (fun t => Kh (A t) (Q t) (J t)) t0 :=
  anal_apply (anal_adjoint (analyticAt_Hh hA hQ)) hJ

theorem analyticAt_Bt (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) (hC : AnalyticAt ℝ Cb t0)
    (hJ : AnalyticAt ℝ J t0) : AnalyticAt ℝ (fun t => Bt (A t) (Q t) (Cb t) (J t)) t0 :=
  ((analyticAt_cdet (analyticAt_Mc hA hQ)).smul hA).sub
    ((analyticAt_lam hC (analyticAt_Kh hA hQ hJ)).const_smul (c := (2 : ℝ)))

theorem analyticAt_Nh (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) (hC : AnalyticAt ℝ Cb t0)
    (hJ : AnalyticAt ℝ J t0) : AnalyticAt ℝ (fun t => Nh (A t) (Q t) (Cb t) (J t)) t0 :=
  anal_comp (anal_comp hQ (analyticAt_cadj (analyticAt_Bt hA hQ hC hJ))) (anal_adjoint hQ)

/-- **`Dcore` is analytic wherever the core data are.** -/
theorem analyticAt_Dcore (hA : AnalyticAt ℝ A t0) (hQ : AnalyticAt ℝ Q t0) (hC : AnalyticAt ℝ Cb t0)
    (hJ : AnalyticAt ℝ J t0) : AnalyticAt ℝ (fun t => Dcore (A t) (Q t) (Cb t) (J t)) t0 :=
  (((analyticAt_cdet hA).mul (analyticAt_cdet (analyticAt_Mc hA hQ))).mul
    (analyticAt_cdet (analyticAt_Bt hA hQ hC hJ))).mul (analyticAt_cdet (analyticAt_Nh hA hQ hC hJ))

end Ana

end Core

end AdalyFormal.CoverOmega.Struct
