import NsPtH5
import PSiteC3

/-!
# PtH6a -- the site-level flat row: `Qlev` is a cube average (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

theorem Qlev_flat_cube (G : TowerGeom L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L (G.ell ^ j)) (hfit : ∀ μ, (y μ).val + G.ell ^ j ≤ L μ + 1) (f : SiteL2 L) :
    Qlev G (flatCfg : Cfg L) j y f
      = (1 / (((G.ell ^ j : ℕ)) : ℝ) ^ 3) •
        cube (fun a b c => (WithLp.ofLp f) (mkS L a b c)) (G.ell ^ j) (y 0).val (y 1).val (y 2).val := by
  rw [Qlev_apply]
  have hbg : bgTower G (flatCfg : Cfg L) = fun _ => trivialU L :=
    funext (fun i => bgTower_flat G i)
  rw [hbg, AdalyFormal.SiteCoercivity.Qflat_eq_blockMean G.ell hell _ j y hy]
  rw [sum_block_eq_cube y (G.ell ^ j) hfit (WithLp.ofLp f)]

#print axioms Qlev_flat_cube

end AdalyFormal.CoverOmega
