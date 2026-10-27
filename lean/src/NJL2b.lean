import NJL2a

/-!
# NJL2b -- (volume-free L2, step 2) the axial staircase depends only on the offset, and the far contour is the same staircase.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq)
open SmallnessBridge.Assemble (coarseCoordSteps_update_ne)

variable {L : PeriodicLatticeExtent}

/-- the staircase with offset `d`. -/
def stair (d : PeriodicLatticeSite L) : List (Fin 3) :=
  List.replicate (d 2).val 2 ++ (List.replicate (d 1).val 1 ++ List.replicate (d 0).val 0)

theorem coarseGammaPath_one_eq_stair (y x : PeriodicLatticeSite L) :
    coarseGammaPath 1 y x = stair (x - y) := by
  have h1 : coarseCoordSteps 1 (Function.update y 2 (x 2)) x 1 = coarseCoordSteps 1 y x 1 :=
    coarseCoordSteps_update_ne 1 y x (x 2) (by decide : (1 : Fin 3) ≠ 2)
  have h0a : coarseCoordSteps 1 (Function.update y 2 (x 2)) x 0 = coarseCoordSteps 1 y x 0 :=
    coarseCoordSteps_update_ne 1 y x (x 2) (by decide : (0 : Fin 3) ≠ 2)
  have h0 : coarseCoordSteps 1 (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
      = coarseCoordSteps 1 y x 0 := by
    rw [coarseCoordSteps_update_ne 1 (Function.update y 2 (x 2)) x (x 1)
      (by decide : (0 : Fin 3) ≠ 1), h0a]
  unfold coarseGammaPath coarseStraightSegment
  rw [h1, h0]
  unfold stair coarseCoordSteps
  simp only [Nat.div_one, Pi.sub_apply]

theorem pathSite_eq_add (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    pathSite x μ n = x + n • Pi.single μ 1 := by
  rw [pathSite_eq]
  funext ν
  by_cases h : ν = μ
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

theorem partner_sub_cPlus (u c : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    pathSite u μ n - pathSite c μ n = u - c := by
  rw [pathSite_eq_add, pathSite_eq_add]
  abel

#print axioms coarseGammaPath_one_eq_stair
#print axioms partner_sub_cPlus

end AdalyFormal.NonflatJet
