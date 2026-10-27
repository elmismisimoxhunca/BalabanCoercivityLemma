import CB10
/-!
# CB11 -- must-fire controls for the cone predicates (kernel `decide`)

The level-1, `ell = 2` cone of the origin bond in direction `0` on the 6×6×6 torus is NOT contained in
`Bsmall1` (direction coordinate `≤ 1`) nor in `Bsmall2` (all coordinates `≤ 1`): `goodB` is refuted
outright.  Together with `cone_goodB` (CB10) this shows the predicate discriminates regions.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement

def Bsmall1 (e : PeriodicLatticeEdge L6) : Prop := (∀ μ : Fin 3, (e.1 μ).val ≤ 3) ∧ (e.1 e.2).val ≤ 1
def Bsmall2 (e : PeriodicLatticeEdge L6) : Prop := (∀ μ : Fin 3, (e.1 μ).val ≤ 1) ∧ (e.1 e.2).val ≤ 2

instance : DecidablePred Bsmall1 := fun e => by unfold Bsmall1; infer_instance
instance : DecidablePred Bsmall2 := fun e => by unfold Bsmall2; infer_instance
instance : DecidablePred (plaqIn Bsmall1) := fun t => by unfold plaqIn; infer_instance
instance : DecidablePred (plaqIn Bsmall2) := fun t => by unfold plaqIn; infer_instance

theorem cone_not_small1 : ¬ goodB 2 (plaqIn Bsmall1) 1 (o6, 0) := by
  simp only [goodB, goodP, implies_true, true_and]
  decide +kernel

theorem cone_not_small2 : ¬ goodB 2 (plaqIn Bsmall2) 1 (o6, 0) := by
  simp only [goodB, goodP, implies_true, true_and]
  decide +kernel

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.cone_not_small1
#print axioms AdalyFormal.CurvBlock.cone_not_small2
