import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.AdmissibleSubspace

/-! # NJ3Base -- restriction of a bond field to `CoarseBond L 1` (every site is 1-coarse). -/
set_option autoImplicit false
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- restriction of a bond field to `CoarseBond L 1` (every site is 1-coarse). -/
def bondToUnit (B : Bond L → SuTwo) : CoarseBond L 1 → SuTwo := fun b => B (b.1.1, b.2)

/-- the index bridge `CoarseBond L ell ≃ CoarseBond L (1 * ell)`. -/
def cbEquiv (ell : ℕ) : CoarseBond L ell ≃ CoarseBond L (1 * ell) where
  toFun c := ⟨⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2⟩
  invFun c := ⟨⟨c.1.1, by simpa [one_mul] using c.1.2⟩, c.2⟩
  left_inv c := rfl
  right_inv c := rfl

end AdalyFormal.NonflatJet
