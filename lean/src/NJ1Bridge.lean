import R2RawX
import M2Proof

/-!
# NJ1Bridge -- the R2 raw one-step map `rawStep` IS the SI1 `modifiedAverageS` (CMP98 (63)/(89)), any stride

Group-level equality `rawStep s ell V0 V1 c = modifiedAverageS s V0 ell V1 c`, via
(i) `rProd = rZeroPathS` (both are the ordered conjugated product (58); R2 telescopes it, SI1 folds it),
(ii) `su2Exp (-X) = (su2Exp X)⁻¹` on `su(2)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.IngredientFamilyR2 (rProd rawStep sBlock rProd_eq)
open AdalySI1.Multiscale.M1 (rZeroPathS rZeroPathStepS endpointAvgS modifiedAverageS)
open AdalySI1.ModifiedAverageDeriv (configMul groupConj)

variable {L : PeriodicLatticeExtent}

theorem foldl_rZeroPathStepS (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (p : List (Fin 3)) :
    ∀ (y : PeriodicLatticeSite L) (h pr : SU2),
      (p.foldl (rZeroPathStepS s V0 V1) (y, h, pr)).2.2
        = pr * (h * coarsePathHolonomy s (fun b => V1 b * V0 b) y p
            * (coarsePathHolonomy s V0 y p)⁻¹ * h⁻¹) := by
  induction p with
  | nil => intro y h pr; simp [coarsePathHolonomy]
  | cons μ rest ih =>
      intro y h pr
      rw [List.foldl_cons]
      show (rest.foldl (rZeroPathStepS s V0 V1)
        (coarseShift y s μ, h * V0 (y, μ), pr * groupConj h (V1 (y, μ)))).2.2 = _
      rw [ih]
      simp only [coarsePathHolonomy, groupConj, mul_inv_rev]
      group

theorem rProd_eq_rZeroPathS (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    rProd s V0 V1 y p = rZeroPathS s V0 V1 y p := by
  rw [rProd_eq]
  unfold rZeroPathS
  rw [foldl_rZeroPathStepS]
  simp

theorem su2Exp_neg_of_mem {X : M2} (hah : Xᴴ = -X) (htr : Matrix.trace X = 0) :
    su2Exp (-X) = (su2Exp X)⁻¹ := by
  have hah' : (-X)ᴴ = -(-X) := by rw [Matrix.conjTranspose_neg, hah]
  have htr' : Matrix.trace (-X) = 0 := by rw [Matrix.trace_neg, htr, neg_zero]
  apply Subtype.ext
  rw [AdalyFormal.Balaban.SmoothLog.su2Exp_coe_of_mem_suTwo hah' htr']
  rw [coe_inv, AdalyFormal.Balaban.SmoothLog.su2Exp_coe_of_mem_suTwo hah htr]
  rw [← Matrix.exp_conjTranspose, hah]

#print axioms foldl_rZeroPathStepS
#print axioms rProd_eq_rZeroPathS
#print axioms su2Exp_neg_of_mem

theorem sBlock_mem (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    (sBlock s ell V0 V1 y)ᴴ = -(sBlock s ell V0 V1 y) ∧ Matrix.trace (sBlock s ell V0 V1 y) = 0 :=
  AdalyFormal.IngredientFamilyR2.sum_qsmul_su2Log_mem _ _ _

theorem endpointAvgS_eq_su2Exp_sBlock (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) :
    endpointAvgS s V0 V1 ell y = su2Exp (sBlock s ell V0 V1 y) := by
  unfold endpointAvgS sBlock
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [rProd_eq_rZeroPathS]

/-- **THE BRIDGE.**  R2's raw one-step map IS SI1's `modifiedAverageS`, at every stride, background,
field and bond. -/
theorem rawStep_eq_modifiedAverageS (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    rawStep s ell V0 V1 c = modifiedAverageS s V0 ell V1 c := by
  unfold rawStep modifiedAverageS
  rw [endpointAvgS_eq_su2Exp_sBlock, endpointAvgS_eq_su2Exp_sBlock,
    ← su2Exp_neg_of_mem (sBlock_mem s ell V0 V1 c.1).1 (sBlock_mem s ell V0 V1 c.1).2]
  unfold groupConj ubarSU2 configMul
  rfl

#print axioms rawStep_eq_modifiedAverageS

end AdalyFormal.NonflatJet
