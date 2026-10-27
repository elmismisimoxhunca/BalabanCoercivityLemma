import NJE3
import NJ1Bridge

/-!
# NJE4 -- THE STRIDE REDUCTION: `rawStep s ell V0 V1 (embE c') = rawStep 1 ell (resV V0) (resV V1) c'`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS loopVar gammaVarStrided coarseBondVar stridedBlockedGauge)
open AdalyFormal.IngredientFamilyR2 (rProd rawStep sBlock rProd_eq)

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

theorem loopVar_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge Lq) (x : PeriodicLatticeSite Lq) :
    loopVar s ell V (embE hs c) (embS hs x) = loopVar 1 ell (resV hs V) c x := by
  unfold loopVar gammaVarStrided coarseBondVar
  show _ = _
  rw [show (embE hs c).1 = embS hs c.1 from rfl, show (embE hs c).2 = c.2 from rfl, cPlusS_emb,
    coarseGammaPath_emb, hol_emb, hol_emb, hol_emb, hol_emb]

theorem stridedBlockedGauge_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ)
    (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge Lq) :
    stridedBlockedGauge su2LogExp s ell V (embE hs c)
      = stridedBlockedGauge su2LogExp 1 ell (resV hs V) c := by
  unfold stridedBlockedGauge
  show su2LogExp.exp (∑ x ∈ stepBlockOf (embS hs c.1) s ell, ((ell : ℚ) ^ 3)⁻¹ •
      su2LogExp.log (loopVar s ell V (embE hs c) x)) * coarseBondVar s ell V (embE hs c) = _
  rw [stepBlockOf_emb, Finset.sum_image (fun a _ b _ h => embS_injective hs h)]
  simp only [loopVar_emb]
  congr 1
  unfold coarseBondVar
  show coarsePathHolonomy s V (embS hs c.1) _ = _
  rw [hol_emb]
  rfl

theorem sBlock_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ)
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite Lq) :
    sBlock s ell V0 V1 (embS hs y) = sBlock 1 ell (resV hs V0) (resV hs V1) y := by
  unfold sBlock
  rw [stepBlockOf_emb, Finset.sum_image (fun a _ b _ h => embS_injective hs h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [coarseGammaPath_emb, rProd_eq, rProd_eq, hol_emb, hol_emb]
  rfl

theorem rawStep_emb (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ)
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge Lq) :
    rawStep s ell V0 V1 (embE hs c) = rawStep 1 ell (resV hs V0) (resV hs V1) c := by
  unfold rawStep
  have h1 := stridedBlockedGauge_emb hs ell V0 c
  have h2 := stridedBlockedGauge_emb hs ell (fun b => V1 b * V0 b) c
  have h3 : sBlock s ell V0 V1 (embE hs c).1 = sBlock 1 ell (resV hs V0) (resV hs V1) c.1 :=
    sBlock_emb hs ell V0 V1 c.1
  have h4 : sBlock s ell V0 V1 (cPlusS s ell (embE hs c))
      = sBlock 1 ell (resV hs V0) (resV hs V1) (cPlusS 1 ell c) := by
    rw [cPlusS_emb]; exact sBlock_emb hs ell V0 V1 _
  rw [h1, h2, h3, h4]
  rfl

#print axioms loopVar_emb
#print axioms stridedBlockedGauge_emb
#print axioms sBlock_emb
#print axioms rawStep_emb

end AdalyFormal.NonflatJet
