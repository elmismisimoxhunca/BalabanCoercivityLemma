import ZT5D

/-!
# ZT5E -- must-fire controls for (3): a coarse row `c` that touches `Λ'` only through `c₊`.

Instance: unit torus `Lu` (60 sites), `Λ = LamT = {30 ≤ y₀ < 34}`, `Λ' = {coarse y : y₀ ∈ {30, 32}}`, the row `c = ((28,0,0), e₀)`: `c₋ = (28,0,0) ∉ Λ'`,
`c₊ = (30,0,0) ∈ Λ'`.  Under the r2..r4 definition (`c₋ ∈ Λ'` only) this row is NOT a dropped row; under r5 it is, `C` solves `(Q₁ B)(c) = 0` for it
(`Cop_ker`), and at the flat background the constraint is the nonzero scalar `ell⁻³ = 1/8` on its dropped bond.  A definitional mutant restoring `c₋`-only
makes `touching_row_*` fail to elaborate (`ZStatementP428.droppedBond_of_cplus` fails first).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

/-- the site `(28,0,0)` of the 60-torus -/
def y28 (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : PeriodicLatticeSite Lu :=
  fun μ => ⟨if μ = 0 then 28 else 0, by have := hLu μ; split_ifs <;> omega⟩

theorem y28_coarse {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    y28 Lu hLu ∈ CoarseLattice Lu 2 := by
  rw [mem_CoarseLattice]
  intro μ
  show (if μ = 0 then 28 else 0) % 2 = 0
  split_ifs <;> norm_num

/-- the row `c = ((28,0,0), e₀)` -/
def row28 (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : CoarseBond Lu 2 :=
  (⟨y28 Lu hLu, y28_coarse hLu⟩, (0 : Fin 3))

theorem row28_minus_not_mem {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    (row28 Lu hLu).1.1 ∉ LamPrime 2 (LamT Lu) := by
  rintro ⟨-, hblk⟩
  have hself : (row28 Lu hLu).1.1 ∈ blockOf (row28 Lu hLu).1.1 2 := by
    rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by omega⟩
  have := hblk _ hself
  simp only [LamT, Set.mem_setOf_eq] at this
  have h0 : ((row28 Lu hLu).1.1 0).val = 28 := by simp [row28, y28]
  omega

theorem row28_plus_mem {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    coarseShift (row28 Lu hLu).1.1 2 (row28 Lu hLu).2 ∈ LamPrime 2 (LamT Lu) := by
  have hv0 : ((coarseShift (row28 Lu hLu).1.1 2 0) 0).val = 30 := by
    rw [coarseShift_val_eq]
    have : ((row28 Lu hLu).1.1 0).val = 28 := by simp [row28, y28]
    rw [this, hLu 0]
  have hv : ∀ ν : Fin 3, ν ≠ 0 → ((coarseShift (row28 Lu hLu).1.1 2 0) ν).val = 0 := by
    intro ν hν
    rw [coarseShift_apply_ne _ _ _ _ hν]
    simp [row28, y28, hν]
  refine ⟨?_, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    by_cases h : μ = 0
    · subst h; show ((coarseShift (row28 Lu hLu).1.1 2 0) 0).val % 2 = 0; rw [hv0]
    · show ((coarseShift (row28 Lu hLu).1.1 2 0) μ).val % 2 = 0; rw [hv μ h]
  · intro x hx
    rw [mem_blockOf] at hx
    have := (hx 0).1
    have h2 := (hx 0).2
    simp only [LamT, Set.mem_setOf_eq]
    show 30 ≤ (x 0).val ∧ (x 0).val < 34
    have e : ((coarseShift (row28 Lu hLu).1.1 2 (row28 Lu hLu).2) 0).val = 30 := hv0
    omega

/-- the row touches `Λ'` (through `c₊` only) -/
theorem row28_cRowIn {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    CRowIn 2 (LamT Lu) (row28 Lu hLu) := Or.inr (row28_plus_mem hLu)

/-- **MUST-FIRE (3), part 1**: the dropped bond of the touching-only row IS dropped under r5 (false under the `c₋`-only definition). -/
theorem touching_row_dropped {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    IsDroppedIn (LamT Lu) 2 (AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast 2 (row28 Lu hLu)) :=
  droppedBond_of_cplus (LamT Lu) 2 _ (row28_plus_mem hLu)

/-- **MUST-FIRE (3), part 2**: `C` solves the constraint on the touching-only row: `(Q₁ (C B))(c) = 0` for EVERY `B` (flat `Q₁`). -/
theorem touching_row_ker {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (B : Bond Lu → SuTwo) :
    (q1SU2 2) (Cop (LamT Lu) (q1SU2 2) B) (row28 Lu hLu) = 0 := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; norm_num
  exact Cop_ker (LamT Lu) (q1SU2 2) (H0_q1SU2_bijective (by norm_num) hdvd (LamT Lu)) B (row28 Lu hLu)
    (row28_cRowIn hLu)

/-- **MUST-FIRE (3), part 3**: the constraint on the touching-only row is a NONZERO scalar (`ell⁻³ = 1/8`) on its own dropped bond, so
leaving the row out of `Dset` (r2..r4) leaves a genuine equation unsolved. -/
theorem touching_row_scalar {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (w : Dset Lu 2 (LamT Lu) → SuTwo) :
    H0 (LamT Lu) (q1SU2 2) w ⟨row28 Lu hLu, row28_cRowIn hLu⟩
      = ((1 : ℝ) / 8) • w ⟨row28 Lu hLu, row28_cRowIn hLu⟩ := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; norm_num
  rw [H0_q1SU2_apply (by norm_num) hdvd (LamT Lu) w _]
  norm_num

#print axioms row28_plus_mem
#print axioms row28_minus_not_mem
#print axioms touching_row_dropped
#print axioms touching_row_ker
#print axioms touching_row_scalar

end AdalyFormal.StatementLaneG
