import TL5b

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.IngredientFamilyR2

theorem phiS_shiftBack {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    phiS h o (periodicLatticeShiftBack x μ) = periodicLatticeShiftBack (phiS h o x) μ := by
  apply shift_injective _ _ μ
  rw [← phiS_shift, periodicLatticeShift_shiftBack, periodicLatticeShift_shiftBack]

theorem gradAdj_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L)
    (A : BondFnL2 L) :
    gradAdj (pullCfg h o U) (liftF (phiE h o) A) = liftF (phiS h o) (gradAdj U A) := by
  refine PiLp.ext (fun y => ?_)
  have h1 := congrFun (gradAdj_apply (pullCfg h o U) (liftF (phiE h o) A)) y
  have h2 := congrFun (gradAdj_apply U A) (phiS h o y)
  show (WithLp.ofLp (gradAdj (pullCfg h o U) (liftF (phiE h o) A)) y) = (WithLp.ofLp (gradAdj U A)) (phiS h o y)
  rw [h1, h2]
  simp only [AdalyFormal.Balaban.CovariantHjMinimizer.gradCovariantAdjointValue, pullCfg, liftF_apply, phiE]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [phiS_shiftBack]

open Classical in
theorem siteMask_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (S : Set (PeriodicLatticeSite L))
    (f : SiteL2 L) :
    siteMask (phiS h o ⁻¹' S) (liftF (phiS h o) f) = liftF (phiS h o) (siteMask S f) := by
  refine PiLp.ext (fun x => ?_)
  simp only [siteMask_apply, liftF_apply]
  rfl

end AdalyFormal.Thin
