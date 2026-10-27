import GCa3L

/-!
# GCa5 -- A5: unit level `Q1jet`, `C2tilde` (ZXR2Unit1) are gauge-equivariant

Stride 1: `coarseGaugeTransform 1 g V0 = periodicGaugeTransform g V0` (`coarseGaugeTransform_one`,
`rfl`).  Output at the coarse bond `c` is read at the fine edge `(c.1.1, c.2)`, frame `g c.1.1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.GaugeCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (coarseGaugeTransform)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `Ad_g` on coarse-bond fields, frame = base site `c.1.1` of the coarse bond. -/
def adC (g : GaugeFn L) (ell : ℕ) (w : CoarseBond L ell → SuTwo) : CoarseBond L ell → SuTwo :=
  fun c => RMap (g c.1.1) (w c)

theorem suCoordF_gaugeActA (g : GaugeFn L) (B : Bond L → SuTwo) :
    suCoordF (gaugeActA g B) = AdX g (suCoordF B) := by
  funext b
  rw [AdX_apply]
  have e : (⟨toM2 (fromM2 ((B b : SuTwo) : M2)), toM2_mem _⟩ : SuTwo) = B b :=
    Subtype.ext (toM2_fromM2 (B b).2)
  show fromM2 ((RMap (g b.1) (B b) : SuTwo) : M2) = _
  rw [← e]
  rfl

theorem suCoordFInv_AdX (g : GaugeFn L) (x : XS L) :
    suCoordFInv (AdX g x) = gaugeActA g (suCoordFInv x) := by
  funext b
  apply Subtype.ext
  show toM2 (fromM2 ((RMap (g b.1) ⟨toM2 (x b), toM2_mem _⟩ : SuTwo) : M2))
    = ((RMap (g b.1) ⟨toM2 (x b), toM2_mem _⟩ : SuTwo) : M2)
  exact toM2_fromM2 (RMap _ _).2

/-- **A5 (first order).** -/
theorem Q1jet_gauge (ell : ℕ) (g : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L)
    (B : Bond L → SuTwo) :
    Q1jet ell (periodicGaugeTransform g V0) (gaugeActA g B) = adC g ell (Q1jet ell V0 B) := by
  funext c
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell (coarseGaugeTransform 1 g V0)
      (suCoordF (gaugeActA g B)))) (c.1.1, c.2)
    = RMap (g c.1.1) (((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell V0 (suCoordF B))) (c.1.1, c.2))
  rw [suCoordF_gaugeActA, QlinStepL_gauge, suCoordFInv_AdX, map_smul]
  rfl

/-- **A5 (second order).** -/
theorem C2tilde_gauge (ell : ℕ) (g : GaugeFn L) (V0 : PeriodicLinkConfiguration SU2 L)
    (B : Bond L → SuTwo) :
    C2tilde ell (periodicGaugeTransform g V0) (gaugeActA g B) = adC g ell (C2tilde ell V0 B) := by
  funext c
  show (suCoordFInv (C2StepL 1 ell (coarseGaugeTransform 1 g V0)
      (suCoordF (gaugeActA g B)))) (c.1.1, c.2)
    = RMap (g c.1.1) ((suCoordFInv (C2StepL 1 ell V0 (suCoordF B))) (c.1.1, c.2))
  rw [suCoordF_gaugeActA, C2StepL_gauge, suCoordFInv_AdX]
  rfl

#print axioms Q1jet_gauge
#print axioms C2tilde_gauge

end AdalyFormal.GaugeCov
