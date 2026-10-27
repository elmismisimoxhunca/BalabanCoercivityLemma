import TL10d
import R2RawX

/-!
# TL11a -- the raw one-step averaging `V̿` is natural at aligned bonds
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar UbarTower cPlusS_eq)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp SU2 M2)
open AdalyFormal.IngredientFamilyR2

section raw
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}

theorem rProdAux_nat (hp : PhiOK h o s)
    {V0t V1t : PeriodicLinkConfiguration SU2 Lt} {V0 V1 : PeriodicLinkConfiguration SU2 L}
    (h0 : AgreeAligned h o s V0t V0) (h1 : AgreeAligned h o s V1t V1) (p : List (Fin 3)) :
    ∀ (g : SU2) (y : PeriodicLatticeSite Lt), Aligned s y → rProdAux s V0t V1t g y p = rProdAux s V0 V1 g (phiS h o y) p := by
  induction p with
  | nil => intro g y _; rfl
  | cons μ rest ih =>
    intro g y hy
    simp only [rProdAux]
    rw [h0 (y, μ) hy, h1 (y, μ) hy, ← coarseShift_nat, ih _ _ (aligned_coarseShift (fun μ => (hp.side μ).trans (h μ)) hy μ)]
    rfl

theorem sBlock_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t V1t : PeriodicLinkConfiguration SU2 Lt} {V0 V1 : PeriodicLinkConfiguration SU2 L}
    (h0 : AgreeAligned h o s V0t V0) (h1 : AgreeAligned h o s V1t V1) {y : PeriodicLatticeSite Lt}
    (hy : Aligned (s * ell) y) : sBlock s ell V0t V1t y = sBlock s ell V0 V1 (phiS h o y) := by
  unfold sBlock
  rw [← stepBlock_sum hp hs hell hy (fun w => ((ell : ℚ) ^ 3)⁻¹ • su2Log (rProd s V0 V1 (phiS h o y) (coarseGammaPath s (phiS h o y) w)))]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  unfold rProd
  rw [coarseGammaPath_nat hp hs hell hy hx, rProdAux_nat (hp.mono (Dvd.intro ell rfl)) h0 h1 _ _ _ (aligned_of_mul hy)]

theorem agreeAligned_mul {s : ℕ} {V0t V1t : PeriodicLinkConfiguration SU2 Lt} {V0 V1 : PeriodicLinkConfiguration SU2 L}
    (h0 : AgreeAligned h o s V0t V0) (h1 : AgreeAligned h o s V1t V1) :
    AgreeAligned h o s (fun b => V1t b * V0t b) (fun b => V1 b * V0 b) := by
  intro e he
  show V1t e * V0t e = V1 (phiE h o e) * V0 (phiE h o e)
  rw [h0 e he, h1 e he]

theorem rawStep_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t V1t : PeriodicLinkConfiguration SU2 Lt} {V0 V1 : PeriodicLinkConfiguration SU2 L}
    (h0 : AgreeAligned h o s V0t V0) (h1 : AgreeAligned h o s V1t V1) {c : PeriodicLatticeEdge Lt}
    (hc : Aligned (s * ell) c.1) :
    rawStep s ell V0t V1t c = rawStep s ell V0 V1 (phiE h o c) := by
  have hcp : Aligned (s * ell) (cPlusS s ell c) := aligned_cPlusS (fun μ => (hp.side μ).trans (h μ)) hc
  unfold rawStep
  rw [sBlock_nat hp hs hell h0 h1 hc, sBlock_nat hp hs hell h0 h1 hcp, cPlusS_nat,
    stridedBlockedGauge_nat su2LogExp hp hs hell (agreeAligned_mul h0 h1) hc,
    stridedBlockedGauge_nat su2LogExp hp hs hell h0 hc]
  rfl

theorem expCfgX_agree {s : ℕ} (a : XS Lt) (b : XS L) (hab : ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → a e = b (phiE h o e)) :
    AgreeAligned h o s (expCfgX a) (expCfgX b) := by
  intro e he
  simp only [expCfgX]
  rw [hab e he]

theorem qStepX_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    (a : XS Lt) (b : XS L) (hab : ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → a e = b (phiE h o e))
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) :
    qStepX s ell V0t a c = qStepX s ell V0 b (phiE h o c) := by
  unfold qStepX
  rw [rawStep_nat hp hs hell h0 (expCfgX_agree a b hab) hc]

end raw


end AdalyFormal.Thin
