import NJ3Base
import ESmall

/-!
# NJ4Li -- sup-norm bound of the covariant line integral (volume-free)

`‖lineIntegral ell V A y p‖ ≤ |p| · M` whenever every bond value of `A` has norm `≤ M` (each term is a bond value or its isometric transport).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem norm_lineIntegral_le (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L ell → SuTwo) (M : ℝ) (hM : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M)
    (p : List (Fin 3)) : ∀ y : PeriodicLatticeSite L, ‖lineIntegral ell V A y p‖ ≤ p.length * M := by
  induction p with
  | nil => intro y; simp
  | cons μ rest ih =>
      intro y
      rw [lineIntegral_cons]
      have h1 : ‖(if h : y ∈ CoarseLattice L ell then A (⟨y, h⟩, μ) else 0)‖ ≤ M := by
        by_cases h : y ∈ CoarseLattice L ell
        · rw [dif_pos h]; exact hA _
        · rw [dif_neg h]; simpa using hM
      have h2 : ‖AdalyFormal.Balaban.CovariantOperators.RMap (V (y, μ))
          (lineIntegral ell V A (coarseShift y ell μ) rest)‖ ≤ rest.length * M := by
        rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]; exact ih _
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ M + rest.length * M := add_le_add h1 h2
        _ = ((μ :: rest).length : ℝ) * M := by simp [List.length_cons]; ring

#print axioms norm_lineIntegral_le

end AdalyFormal.NonflatJet
