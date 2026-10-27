import TL8d

/-!
# TL9a -- `Q'_j(U)` rows are natural at the sites of `Λ_j`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.IngredientFamilyR2

section q
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {ell k : ℕ}

theorem Qlev_nat (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) {j : ℕ} (hj : j ≤ k)
    (f : SiteL2 L) {y : PeriodicLatticeSite Lt} (hy : y ∈ (geomOf ell k (towerPull h o S)).Lam j) :
    Qlev (geomOf ell k (towerPull h o S)) (pullCfg h o U) j y (liftF (phiS h o) f) = Qlev (geomOf ell k S) U j (phiS h o y) f := by
  have hal : Aligned (ell ^ j) y := (Set.mem_setOf_eq.mp hy).1
  rw [Qlev_apply, Qlev_apply]
  show Qcomposite (bgTower _ (pullCfg h o U)) ell j (fun x => (WithLp.ofLp f) (phiS h o x)) y = Qcomposite (bgTower _ U) ell j (WithLp.ofLp f) (phiS h o y)
  exact Qcomposite_nat hell _ _ _ j (phiOK_le (hp := hp) hj) (fun l hl => UbarTower_nat su2LogExp hell U l (phiOK_le (hp := hp) (le_trans (le_of_lt hl) hj))) y hal

end q

end AdalyFormal.Thin
