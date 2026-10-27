import FlatNative
set_option autoImplicit false
namespace HConstruction.DRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.QcEquation (blockCorner blockCorner_mem)
variable {L : PeriodicLatticeExtent}

noncomputable def stepLift (s ell : ℕ) (F : CoarseBond L (s * ell) → SuTwo)
    (e : CoarseBond L s) : SuTwo :=
  if (e.1.1 e.2).val % (s * ell) = s * ell - s then
    (ell : ℝ) • F (⟨blockCorner (s * ell) e.1.1, blockCorner_mem _⟩, e.2)
  else 0

theorem stepLift_add (s ell : ℕ) (F G : CoarseBond L (s * ell) → SuTwo) (e : CoarseBond L s) :
    stepLift s ell (F + G) e = stepLift s ell F e + stepLift s ell G e := by
  unfold stepLift
  by_cases h : (e.1.1 e.2).val % (s * ell) = s * ell - s
  · rw [if_pos h, if_pos h, if_pos h, Pi.add_apply, smul_add]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem stepLift_smul (s ell : ℕ) (r : ℝ) (F : CoarseBond L (s * ell) → SuTwo)
    (e : CoarseBond L s) : stepLift s ell (r • F) e = r • stepLift s ell F e := by
  unfold stepLift
  by_cases h : (e.1.1 e.2).val % (s * ell) = s * ell - s
  · rw [if_pos h, if_pos h, Pi.smul_apply]
    exact smul_comm _ _ _
  · rw [if_neg h, if_neg h, smul_zero]

end HConstruction.DRepair.Reproduced
