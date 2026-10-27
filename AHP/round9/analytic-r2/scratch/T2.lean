import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
#check @sum_apply
#check @ContinuousLinearMap.coe_sum'
#check @ContinuousLinearMap.sum_apply
#check @continuous_finsetSum
#check @AdalyFormal.IngredientFamilyR2.Qlev_apply
#check @AdalyFormal.Balaban.QjComposite.Qcomposite_succ
#check @AdalyFormal.M1Site.QpP_inr
#check @AdalyFormal.M1Site.QpP_inl
variable {L : PeriodicLatticeExtent}
example (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam =
      AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ 0) (bg 0) ell lam := rfl
example (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl
