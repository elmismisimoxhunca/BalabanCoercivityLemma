import GCa1
import GCa2
import GC3
import ZXR2Unit1

/-!
# GCa3 -- `AdX γ` on coordinate fields `XS L`; nonlinear equivariance of `qStepX`, `qCompX`;
equivariance of the jets `QlinStepX`, `C2StepX`, `QlinCompX`, `C2CompX`; `bgTower_gauge` (A1).

`AdX γ = eX ∘ adBL γ ∘ eX⁻¹` with `eX = (suCoord, suCoordInv) : BondFnL2 L ≃ₗ XS L`, so
`(AdX γ a) b = fromM2 (R(γ b₋) ⟨toM2 (a b), _⟩)` (`AdX_apply`, `rfl`).
The output of `qStepX` at bond `c` is read in the frame `γ c₋` -- the same operator `AdX γ` on input
and output, at every stride `s`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 adMap adMap_apply su2_log_conj
  su2_exp_ad)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower_gauge)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `BondFnL2 L ≃ₗ XS L` by the coordinates `fromM2`/`toM2`. -/
def eX : BondFnL2 L ≃ₗ[ℝ] XS L :=
  LinearEquiv.ofLinear suCoord suCoordInv (LinearMap.ext suCoord_suCoordInv)
    (LinearMap.ext suCoordInv_suCoord)

def AdXl (γ : GaugeFn L) : XS L ≃ₗ[ℝ] XS L :=
  (eX.symm.trans (adBL γ).toLinearEquiv).trans eX

/-- `Ad_γ` in coordinates, frame `γ b₋` at bond `b`. -/
def AdX (γ : GaugeFn L) : XS L ≃L[ℝ] XS L := (AdXl γ).toContinuousLinearEquiv

theorem AdX_apply (γ : GaugeFn L) (a : XS L) (b : PeriodicLatticeEdge L) :
    AdX γ a b = fromM2 ((RMap (γ b.1) ⟨toM2 (a b), toM2_mem _⟩ : SuTwo) : M2) := rfl

theorem suCoord_adBL (γ : GaugeFn L) (A : BondFnL2 L) : suCoord (adBL γ A) = AdX γ (suCoord A) := by
  funext b
  rw [AdX_apply]
  have e : (⟨toM2 (fromM2 ((WithLp.ofLp A b : SuTwo) : M2)), toM2_mem _⟩ : SuTwo) = WithLp.ofLp A b :=
    Subtype.ext (toM2_fromM2 (WithLp.ofLp A b).2)
  show fromM2 ((RMap (γ b.1) (WithLp.ofLp A b) : SuTwo) : M2) = _
  rw [← e]
  rfl

theorem suCoordInv_AdX (γ : GaugeFn L) (x : XS L) : suCoordInv (AdX γ x) = adBL γ (suCoordInv x) := by
  refine PiLp.ext (fun b => Subtype.ext ?_)
  show toM2 (fromM2 ((RMap (γ b.1) ⟨toM2 (x b), toM2_mem _⟩ : SuTwo) : M2))
    = ((RMap (γ b.1) ⟨toM2 (x b), toM2_mem _⟩ : SuTwo) : M2)
  exact toM2_fromM2 (RMap _ _).2

theorem expCfgX_AdX (γ : GaugeFn L) (a : XS L) : expCfgX (AdX γ a) = conjCfg γ (expCfgX a) := by
  funext b
  show su2Exp (toM2 (AdX γ a b)) = γ b.1 * su2Exp (toM2 (a b)) * (γ b.1)⁻¹
  rw [AdX_apply, toM2_fromM2 (RMap _ _).2, RMap_coe_apply, ← adMap_apply, su2_exp_ad]

/-- **A2a: `qStepX` is gauge-equivariant, nonlinearly, every `a`, every background.** -/
theorem qStepX_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    qStepX s ell (coarseGaugeTransform s γ V0) (AdX γ a) = AdX γ (qStepX s ell V0 a) := by
  funext c
  rw [AdX_apply]
  show fromM2 (su2Log (rawStep s ell (coarseGaugeTransform s γ V0) (expCfgX (AdX γ a)) c))
    = fromM2 ((RMap (γ c.1) ⟨toM2 (fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c))), toM2_mem _⟩
        : SuTwo) : M2)
  rw [expCfgX_AdX, rawStep_gauge, su2_log_conj, RMap_coe_apply]
  show fromM2 (adMap _ _) = fromM2 (_ * toM2 (fromM2 _) * _)
  rw [toM2_fromM2 (su2Log_mem_suTwo _), adMap_apply]

/-- **A2b: the level composite `qCompX` is equivariant**, for any tower `bg'` that is the stride-wise
gauge transform of `bg`. -/
theorem qCompX_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) :
    ∀ j a, qCompX ell bg' j (AdX γ a) = AdX γ (qCompX ell bg j a) := by
  intro j
  induction j with
  | zero => intro a; rfl
  | succ j ih =>
      intro a
      simp only [qCompX, Function.comp_apply]
      rw [ih, hbg, qStepX_gauge]

theorem QlinStepX_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    QlinStepX s ell (coarseGaugeTransform s γ V0) (AdX γ a) = AdX γ (QlinStepX s ell V0 a) := by
  have h := fderiv_equivariant (AdX γ) (qStepX s ell V0) (qStepX s ell (coarseGaugeTransform s γ V0))
    (qStepX_gauge s ell γ V0) 0 a
  rw [map_zero] at h
  exact h

theorem C2StepX_gauge (s ell : ℕ) (γ : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L) (a : XS L) :
    C2StepX s ell (coarseGaugeTransform s γ V0) (AdX γ a) = AdX γ (C2StepX s ell V0 a) := by
  have h := fderiv2_equivariant (AdX γ) (qStepX s ell V0) (qStepX s ell (coarseGaugeTransform s γ V0))
    (qStepX_gauge s ell γ V0) 0 a a
  rw [map_zero] at h
  unfold C2StepX
  rw [map_smul, h]

/-- **A3: the first-order jet of the composite is equivariant.** -/
theorem QlinCompX_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) (j : ℕ) (a : XS L) :
    QlinCompX ell bg' j (AdX γ a) = AdX γ (QlinCompX ell bg j a) := by
  have h := fderiv_equivariant (AdX γ) (qCompX ell bg j) (qCompX ell bg' j)
    (qCompX_gauge ell bg bg' γ hbg j) 0 a
  rw [map_zero] at h
  exact h

/-- **A3: the second-order jet of the composite is equivariant.** -/
theorem C2CompX_gauge (ell : ℕ) (bg bg' : ℕ → PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L)
    (hbg : ∀ j, bg' j = coarseGaugeTransform (ell ^ j) γ (bg j)) (j : ℕ) (a : XS L) :
    C2CompX ell bg' j (AdX γ a) = AdX γ (C2CompX ell bg j a) := by
  have h := fderiv2_equivariant (AdX γ) (qCompX ell bg j) (qCompX ell bg' j)
    (qCompX_gauge ell bg bg' γ hbg j) 0 a a
  rw [map_zero] at h
  unfold C2CompX
  rw [map_smul, h]

/-- **A1.** -/
theorem bgTower_gauge (G : TowerGeom L) (U : Cfg L) (γ : GaugeFn L) (j : ℕ) :
    bgTower G (periodicGaugeTransform γ U) j = coarseGaugeTransform (G.ell ^ j) γ (bgTower G U j) :=
  UbarTower_gauge su2LogExp G.ell γ U j

#print axioms suCoord_adBL
#print axioms suCoordInv_AdX
#print axioms qStepX_gauge
#print axioms qCompX_gauge
#print axioms QlinStepX_gauge
#print axioms C2StepX_gauge
#print axioms QlinCompX_gauge
#print axioms C2CompX_gauge
#print axioms bgTower_gauge

end AdalyFormal.GaugeCov
