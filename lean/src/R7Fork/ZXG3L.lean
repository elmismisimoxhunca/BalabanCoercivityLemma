import R7Fork.ZXG3K
import R7Fork.ZXG3J1

/-!
# G3L -- THE CLOSED POINT OF THE GENUINE CLAIM (general torus): `ell = 2`, `k = 0`, any unit torus `Lu`
with `4 ≤ Lu μ` and `2 ∣ Lu μ + 1`, full tower, `Λ = univ`, flat `U`, any `a > 0`.  For EVERY `B̃` in the
statement's class `Λ̃` (the axial staircases and the dropped bonds vanish):
   `(1/1728)·‖B̃‖² ≤ (3.156)(C B̃)`        (genuine form `genForm`, genuine `C = Cop`).
Composition: (i) `C B̃` is axial and in `ker Q₁` (ingredient lane `Cop_id`, `Cop_ker` + tree
`droppedBondLast_not_mem_staircase`), (ii) the tree's CMP96 Lemma 2.4 at `U = 1` (`lemma24_flat`),
(iii) transport fine ↔ unit torus at `k = 0` (G3K), (iv) the reduction
`(3.156) = ⟨x,Δ_π x⟩ + ‖R D* x‖² ≥ ‖curl x‖²` (G3C `P0_genForm_eq`, `inner_DpiFull_flat`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 600000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath mem_CoarseLattice)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast droppedBondLast_not_mem_staircase)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)

section
variable (Lu : PeriodicLatticeExtent)

open AdalyFormal.IngredientFamily (q1SU2)

/-- `C B̃` for `B̃ ∈ Λ̃` (`Λ = univ`, `ell = 2`, `C = id − h Q₁`) is axial, lies in `ker Q₁`, and
`‖B̃‖ ≤ ‖C B̃‖` -/
theorem Cop_props_univ (hd : ∀ μ, 2 ∣ Lu μ + 1)
    (hb : Function.Bijective (H0 (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2)))
    (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt) :
    (∀ y ∈ CoarseLattice Lu 2, ∀ x ∈ blockOf y 2, ∀ b ∈ staircasePath y x,
        Cop (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) Bt b = 0) ∧
    (∀ c, lineCoarseRestrictSuTwo 2 (Cop (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) Bt) c = 0) ∧
    bondEnergy Bt ≤ ∑ b : Bond Lu, ‖Cop (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) Bt b‖ ^ 2 := by
  have hLP : ∀ y : PeriodicLatticeSite Lu, y ∈ CoarseLattice Lu 2 →
      y ∈ LamPrime 2 (Set.univ : Set (PeriodicLatticeSite Lu)) :=
    fun y hy => ⟨hy, fun _ _ => Set.mem_univ _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx b hb'
    have hnd : ¬ IsDroppedIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 b := by
      rintro ⟨c, -, rfl⟩
      exact droppedBondLast_not_mem_staircase (by norm_num) hd c y hy x hx hb'
    rw [Cop_id _ _ Bt b hnd]
    exact hBt.1 y (hLP y hy) x hx b hb'
  · intro c
    exact Cop_ker (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) hb Bt c (Or.inl (hLP c.1.1 c.1.2))
  · unfold bondEnergy
    refine Finset.sum_le_sum (fun b _ => ?_)
    by_cases hd' : IsDroppedIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 b
    · rw [hBt.2 b hd']; simp
    · rw [Cop_id _ _ Bt b hd']

end

#print axioms Cop_props_univ

end AdalyFormal.StatementLaneG
