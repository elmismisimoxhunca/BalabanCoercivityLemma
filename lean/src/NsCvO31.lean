import NsCvO30

/-!
# CvO32 -- the r8 LOCAL jets (`QlinCompL`, `C2CompL`, `D2CompL`) agree with the global jets on a `RegTower2` (lane omega)

`ZLocJet.QlinCompL_eq_QlinCompX` etc. are stated for `RegTower` (loop holonomies near 1).  Here the same bridges for `RegTower2` (loops `≠ -1`), by the same inductions,
using the `RegBg2` smoothness (CvO9).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.IngredientFamilyR2


set_option linter.unusedSectionVars false
variable [CfData]
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.CoverOmega

variable {L : PeriodicLatticeExtent}

theorem QlinStepL_eq_of_reg2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg2 s ell V0) :
    QlinStepL s ell V0 = QlinStepX s ell V0 :=
  QlinStepL_eq_QlinStepX s ell V0 ((qStepX_contDiffAt2 s ell V0 hreg).differentiableAt (by simp))

theorem QlinCompL_eq_QlinCompX2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower2 ell bg J) : ∀ j, j ≤ J → QlinCompL ell bg j = QlinCompX ell bg j := by
  intro j
  induction j with
  | zero => intro _; rw [QlinCompL_zero, QlinCompX_zero_id]
  | succ j ih =>
      intro hj
      rw [QlinCompL_succ, QlinCompX_succ2 ell bg J hreg j (by omega), ih (by omega),
        QlinStepL_eq_of_reg2 _ _ _ (hreg j (by omega))]

theorem C2StepL_eq_C2StepX2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg2 s ell V0) :
    C2StepL s ell V0 = C2StepX s ell V0 := by
  funext a; funext c
  have hg : ContDiffAt ℝ 2 (qStepX s ell V0) 0 := (qStepX_contDiffAt2 s ell V0 hreg).of_le (by simp)
  have hP : ContDiffAt ℝ 2 (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
      (qStepX s ell V0 0) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c).contDiff (n := 2)).contDiffAt
  have hc := AdalyFormal.Balaban.SmoothLog.fderiv_fderiv_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
    (qStepX s ell V0) (0 : XS L) hP hg a a
  have hcomp : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
      ∘ qStepX s ell V0) = qStepComp s ell V0 c := rfl
  rw [hcomp] at hc
  have h2 : fderiv ℝ (fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c))
      (qStepX s ell V0 0) = 0 := by
    have : fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c)
        = fun _ => ContinuousLinearMap.proj c := by
      funext y; exact ContinuousLinearMap.fderiv _
    rw [this]; exact fderiv_const_apply _
  rw [h2, ContinuousLinearMap.fderiv] at hc
  simp only [ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.proj_apply] at hc
  show (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepComp s ell V0 c)) 0 a a = ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 a a) c
  rw [hc]; rfl

theorem C2CompL_eq_C2CompX2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower2 ell bg J) : ∀ j, j ≤ J → C2CompL ell bg j = C2CompX ell bg j := by
  intro j
  induction j with
  | zero => intro _; funext a; rw [C2CompL_zero, C2CompX_zero_eq]
  | succ j ih =>
      intro hj
      funext a
      rw [C2CompL_succ, C2CompX_succ2 ell bg J hreg j (by omega) a, ih (by omega),
        QlinCompL_eq_QlinCompX2 ell bg J hreg j (by omega),
        QlinStepL_eq_of_reg2 _ _ _ (hreg j (by omega)), C2StepL_eq_C2StepX2 _ _ _ (hreg j (by omega))]

#print axioms QlinCompL_eq_QlinCompX2
#print axioms C2CompL_eq_C2CompX2

end AdalyFormal.IngredientFamilyR2
