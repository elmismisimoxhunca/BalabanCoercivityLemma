import NB26
import CB11
/-!
# NB27 -- non-vacuity / must-fire controls for the local cone predicates `GoodPl`, `GoodBd` (kernel decide)

On the 6×6×6 torus, `ell = 2`, level 1, region `B4` = bonds based at coordinates `≤ 4` (a proper subset;
it excludes every bond based at a coordinate `5`), plaquette region `R4 y` = all plaquettes at `y` have
their four bonds in `B4`:
* `goodPl_B4`: the level-1 plaquette cone of the origin is good;
* `goodBd_B4`: the level-1 defect cone of the origin bond in direction 0 is good;
* `not_goodPl_B3`: with bonds based at coordinates `≤ 3` the plaquette cone of the origin is NOT good.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement

def B4 (e : PeriodicLatticeEdge L6) : Prop := ∀ μ : Fin 3, (e.1 μ).val ≤ 4
def B3 (e : PeriodicLatticeEdge L6) : Prop := ∀ μ : Fin 3, (e.1 μ).val ≤ 3
instance : DecidablePred B4 := fun e => by unfold B4; infer_instance
instance : DecidablePred B3 := fun e => by unfold B3; infer_instance
def R4 (y : PeriodicLatticeSite L6) : Prop := ∀ ν μ : Fin 3, plaqIn B4 (y, ν, μ)
def R3 (y : PeriodicLatticeSite L6) : Prop := ∀ ν μ : Fin 3, plaqIn B3 (y, ν, μ)
instance : DecidablePred R4 := fun y => by unfold R4 plaqIn; infer_instance
instance : DecidablePred R3 := fun y => by unfold R3 plaqIn; infer_instance
instance (y z : PeriodicLatticeSite L6) (s B : ℕ) : Decidable (Box y s B z) := by
  unfold Box off; infer_instance

theorem goodPl_B4 : GoodPl 2 R4 1 o6 := by
  simp only [GoodPl]
  decide +kernel

theorem not_goodPl_B3 : ¬ GoodPl 2 R3 1 o6 := by
  simp only [GoodPl]
  decide +kernel

theorem goodBd_B4 : GoodBd 2 R4 1 (o6, 0) := by
  simp only [GoodBd, GoodPl, implies_true, true_and]
  decide +kernel

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.goodPl_B4
#print axioms AdalyFormal.CurvBlock.not_goodPl_B3
#print axioms AdalyFormal.CurvBlock.goodBd_B4
