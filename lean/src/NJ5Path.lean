import NJ4Li
import LoopHolonomySmall

/-!
# NJ5Path -- the FAR contour of (124) (`Γ_{c₊,x'}`) has the same length bound as the near one: `≤ 3(ell-1)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseCoordSteps)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq)
open SmallnessBridge.Assemble (coarseGammaPath_length coarseCoordSteps_update_ne)

variable {L : PeriodicLatticeExtent}

/-- the length of the axial staircase is `≤ 3(ell-1)` once each coordinate step count is `< ell`. -/
theorem coarseGammaPath_one_length_le_of_steps (a b : PeriodicLatticeSite L) {ell : ℕ}
    (h : ∀ ν : Fin 3, coarseCoordSteps 1 a b ν < ell) :
    (coarseGammaPath 1 a b).length ≤ 3 * (ell - 1) := by
  have h1' : coarseCoordSteps 1 (Function.update a 2 (b 2)) b 1 = coarseCoordSteps 1 a b 1 :=
    coarseCoordSteps_update_ne 1 a b (b 2) (by decide : (1 : Fin 3) ≠ 2)
  have h0a : coarseCoordSteps 1 (Function.update a 2 (b 2)) b 0 = coarseCoordSteps 1 a b 0 :=
    coarseCoordSteps_update_ne 1 a b (b 2) (by decide : (0 : Fin 3) ≠ 2)
  have h0' : coarseCoordSteps 1 (Function.update (Function.update a 2 (b 2)) 1 (b 1)) b 0
      = coarseCoordSteps 1 a b 0 := by
    rw [coarseCoordSteps_update_ne 1 (Function.update a 2 (b 2)) b (b 1)
      (by decide : (0 : Fin 3) ≠ 1), h0a]
  rw [coarseGammaPath_length, h1', h0']
  have := h 2; have := h 1; have := h 0
  omega

/-- shifting both endpoints along `μ` by the same amount preserves every coordinate difference. -/
theorem shift_sub_eq (a b : PeriodicLatticeSite L) (μ : Fin 3) (k : ℕ) (ν : Fin 3) :
    (pathSite b μ k ν) - (pathSite a μ k ν) = b ν - a ν := by
  rw [pathSite_eq, pathSite_eq]
  by_cases h : ν = μ
  · subst h
    simp only [Function.update_self]
    abel
  · simp only [Function.update_of_ne h]

theorem coarseCoordSteps_shift (a b : PeriodicLatticeSite L) (μ : Fin 3) (k : ℕ) (ν : Fin 3) :
    coarseCoordSteps 1 (pathSite a μ k) (pathSite b μ k) ν = coarseCoordSteps 1 a b ν := by
  unfold coarseCoordSteps
  rw [shift_sub_eq]

#print axioms coarseGammaPath_one_length_le_of_steps
#print axioms coarseCoordSteps_shift

end AdalyFormal.NonflatJet
