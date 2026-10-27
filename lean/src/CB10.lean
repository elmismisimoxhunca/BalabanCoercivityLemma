import CB9
/-!
# CB10 -- non-vacuity of the local cone on a PROPER region (kernel `decide`)

On the 6×6×6 torus, `Bbox` = bonds based in `[0,3]³` pointing out of a base coordinate `≤ 2` (a proper
subset of the bonds: it excludes every bond based at a coordinate `4` or `5`).  The level-1, `ell = 2`
dependency cones (`goodB`, `goodL`) of the bond at the origin in direction `0` lie in `Bbox`.

No sorry / native_decide / axioms (`decide +kernel` is kernel reduction).
-/
set_option autoImplicit false
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement

abbrev L6 : PeriodicLatticeExtent := fun _ => 5

def Bbox (e : PeriodicLatticeEdge L6) : Prop := (∀ μ : Fin 3, (e.1 μ).val ≤ 3) ∧ (e.1 e.2).val ≤ 2

instance : DecidablePred Bbox := fun e => by unfold Bbox; infer_instance

instance : DecidablePred (plaqIn Bbox) := fun t => by unfold plaqIn; infer_instance

def o6 : PeriodicLatticeSite L6 := fun _ => 0

theorem cone_goodL : goodL 2 Bbox 1 (o6, 0) := by
  simp only [goodL]
  decide +kernel

theorem cone_goodB : goodB 2 (plaqIn Bbox) 1 (o6, 0) := by
  simp only [goodB, goodP, implies_true, true_and]
  decide +kernel

theorem Bbox_proper : ¬ Bbox ((fun _ => (4 : Fin 6)), 0) := by decide

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.cone_goodL
#print axioms AdalyFormal.CurvBlock.cone_goodB
#print axioms AdalyFormal.CurvBlock.Bbox_proper
