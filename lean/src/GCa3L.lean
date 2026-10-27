import GCa3

/-!
# GCa3L -- (r8 transfer, NEW module) gauge equivariance of the r8 LOCAL jets, with NO differentiability hypothesis

r8 defines the averaging jets component by component (`ZLocJet`: `QlinStepL`, `D2StepL`, `C2StepL`, `QlinCompL`, `D2CompL`,
`C2CompL`).  The r7 equivariance theorems of `GCa3` are about the whole-torus jets (`QlinStepX`, ...).  Here the same statements
are proved for the local jets, for EVERY background: the component `c` of `qStepX` is conjugated by the fibre rotation
`adFib γ c` (a continuous linear equivalence of `Fin 3 → ℝ`), and Mathlib's `comp_fderiv`/`comp_right_fderiv` for
continuous linear equivalences need no differentiability.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform)
open AdalyFormal.IngredientFamilyR2

section gen
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem conj_eq_of_equivariant₂ (A : E ≃L[ℝ] E) (B : F ≃L[ℝ] F) (f f' : E → F)
    (h : ∀ x, f' (A x) = B (f x)) : f' = ((B : F → F) ∘ f) ∘ (A.symm : E → E) := by
  funext y
  simp only [Function.comp_apply]
  rw [← h, A.apply_symm_apply]

theorem fderiv_eq_of_equivariant₂ (A : E ≃L[ℝ] E) (B : F ≃L[ℝ] F) (f f' : E → F)
    (h : ∀ x, f' (A x) = B (f x)) :
    fderiv ℝ f' = fun y => A.arrowCongr B (fderiv ℝ f (A.symm y)) := by
  funext y
  rw [conj_eq_of_equivariant₂ A B f f' h, A.symm.comp_right_fderiv, B.comp_fderiv]
  ext v
  simp

/-- first derivative, two different equivalences on source and target; no differentiability. -/
theorem fderiv_equivariant₂ (A : E ≃L[ℝ] E) (B : F ≃L[ℝ] F) (f f' : E → F)
    (h : ∀ x, f' (A x) = B (f x)) (x a : E) : fderiv ℝ f' (A x) (A a) = B (fderiv ℝ f x a) := by
  rw [fderiv_eq_of_equivariant₂ A B f f' h]
  simp

/-- second derivative, two different equivalences; no differentiability. -/
theorem fderiv2_equivariant₂ (A : E ≃L[ℝ] E) (B : F ≃L[ℝ] F) (f f' : E → F)
    (h : ∀ x, f' (A x) = B (f x)) (x a b : E) :
    fderiv ℝ (fderiv ℝ f') (A x) (A a) (A b) = B (fderiv ℝ (fderiv ℝ f) x a b) := by
  have e : fderiv ℝ f'
      = ((A.arrowCongr B : (E →L[ℝ] F) → (E →L[ℝ] F)) ∘ fderiv ℝ f) ∘ (A.symm : E → E) := by
    rw [fderiv_eq_of_equivariant₂ A B f f' h]; rfl
  rw [e, A.symm.comp_right_fderiv, (A.arrowCongr B).comp_fderiv]
  simp
end gen

variable {L : PeriodicLatticeExtent}

theorem AdX_inv_AdX (γ : GaugeFn L) (c : PeriodicLatticeEdge L) (v : Fin 3 → ℝ) :
    AdX (fun x => (γ x)⁻¹) (fun _ => AdX γ (fun _ => v) c) c = v := by
  rw [AdX_apply, AdX_apply]
  have e : (⟨toM2 (fromM2 ((RMap (γ c.1) ⟨toM2 v, toM2_mem _⟩ : SuTwo) : M2)), toM2_mem _⟩ : SuTwo)
      = RMap (γ c.1) ⟨toM2 v, toM2_mem _⟩ := Subtype.ext (toM2_fromM2 (RMap _ _).2)
  rw [e, RMap_mul_apply, inv_mul_cancel, RMap_one]
  exact fromM2_toM2 v

theorem AdX_AdX_inv (γ : GaugeFn L) (c : PeriodicLatticeEdge L) (v : Fin 3 → ℝ) :
    AdX γ (fun _ => AdX (fun x => (γ x)⁻¹) (fun _ => v) c) c = v := by
  rw [AdX_apply, AdX_apply]
  have e : (⟨toM2 (fromM2 ((RMap ((γ c.1)⁻¹) ⟨toM2 v, toM2_mem _⟩ : SuTwo) : M2)), toM2_mem _⟩ : SuTwo)
      = RMap ((γ c.1)⁻¹) ⟨toM2 v, toM2_mem _⟩ := Subtype.ext (toM2_fromM2 (RMap _ _).2)
  rw [e, RMap_mul_apply, mul_inv_cancel, RMap_one]
  exact fromM2_toM2 v

/-- the frame rotation of `AdX γ` at the bond `c`, on one coordinate fibre. -/
def adFib (γ : GaugeFn L) (c : PeriodicLatticeEdge L) : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => AdX γ (fun _ => v) c
      invFun := fun v => AdX (fun x => (γ x)⁻¹) (fun _ => v) c
      map_add' := fun v w => by
        have : (fun _ : PeriodicLatticeEdge L => v + w) = (fun _ => v) + (fun _ => w) := rfl
        rw [this, map_add]; rfl
      map_smul' := fun r v => by
        have : (fun _ : PeriodicLatticeEdge L => r • v) = r • (fun _ => v) := rfl
        rw [this, map_smul]; rfl
      left_inv := fun v => AdX_inv_AdX γ c v
      right_inv := fun v => AdX_AdX_inv γ c v }

theorem AdX_comp (γ : GaugeFn L) (y : XS L) (c : PeriodicLatticeEdge L) : AdX γ y c = adFib γ c (y c) := rfl

theorem qStepComp_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (a : XS L) :
    qStepComp s ell (coarseGaugeTransform s γ V0) c (AdX γ a) = adFib γ c (qStepComp s ell V0 c a) := by
  show qStepX s ell (coarseGaugeTransform s γ V0) (AdX γ a) c = _
  rw [qStepX_gauge, AdX_comp]; rfl

/-- **r8 local one-step jet is gauge-equivariant, every background.** -/
theorem QlinStepL_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    QlinStepL s ell (coarseGaugeTransform s γ V0) (AdX γ a) = AdX γ (QlinStepL s ell V0 a) := by
  funext c
  have h := fderiv_equivariant₂ (AdX γ) (adFib γ c) (qStepComp s ell V0 c)
    (qStepComp s ell (coarseGaugeTransform s γ V0) c) (qStepComp_gauge s ell γ V0 c) 0 a
  rw [map_zero] at h
  rw [QlinStepL_apply, h, AdX_comp, QlinStepL_apply]

theorem D2StepL_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a b : XS L) :
    D2StepL s ell (coarseGaugeTransform s γ V0) (AdX γ a) (AdX γ b) = AdX γ (D2StepL s ell V0 a b) := by
  funext c
  have h := fderiv2_equivariant₂ (AdX γ) (adFib γ c) (qStepComp s ell V0 c)
    (qStepComp s ell (coarseGaugeTransform s γ V0) c) (qStepComp_gauge s ell γ V0 c) 0 a b
  rw [map_zero] at h
  rw [D2StepL_apply, h, AdX_comp, D2StepL_apply]

theorem C2StepL_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    C2StepL s ell (coarseGaugeTransform s γ V0) (AdX γ a) = AdX γ (C2StepL s ell V0 a) := by
  unfold C2StepL
  rw [D2StepL_gauge, map_smul]

/-- **r8 local composite jet is gauge-equivariant** (tower `bg'` = stride-wise transform of `bg`). -/
theorem QlinCompL_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) :
    ∀ j a, QlinCompL ell bg' j (AdX γ a) = AdX γ (QlinCompL ell bg j a) := by
  intro j
  induction j with
  | zero => intro a; rfl
  | succ j ih =>
      intro a
      rw [QlinCompL_succ, QlinCompL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ih, hbg,
        QlinStepL_gauge]

theorem D2CompL_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) :
    ∀ j a b, D2CompL ell bg' j (AdX γ a) (AdX γ b) = AdX γ (D2CompL ell bg j a b) := by
  intro j
  induction j with
  | zero => intro a b; simp [D2CompL]
  | succ j ih =>
      intro a b
      simp only [D2CompL, LinearMap.mk₂_apply]
      rw [ih, QlinCompL_gauge ell bg bg' γ hbg, QlinCompL_gauge ell bg bg' γ hbg, hbg, QlinStepL_gauge, D2StepL_gauge,
        map_add]

theorem C2CompL_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) (j : ℕ) (a : XS L) :
    C2CompL ell bg' j (AdX γ a) = AdX γ (C2CompL ell bg j a) := by
  unfold C2CompL
  rw [D2CompL_gauge ell bg bg' γ hbg, map_smul]

#print axioms fderiv_equivariant₂
#print axioms fderiv2_equivariant₂
#print axioms adFib
#print axioms qStepComp_gauge
#print axioms QlinStepL_gauge
#print axioms D2StepL_gauge
#print axioms C2StepL_gauge
#print axioms QlinCompL_gauge
#print axioms D2CompL_gauge
#print axioms C2CompL_gauge

end AdalyFormal.GaugeCov
