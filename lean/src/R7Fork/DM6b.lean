import R7Fork.DM6

/-!
# DM6b -- the proper multi-stratum tower `TT` (`k = 1`, `ell = 2`, `M = 2`, `R = 6`, `Omega_0 != torus`, `Lambda' != empty`) of `ZT5D`:
all hypotheses of `closed_point_proper_cond` other than the two units hold; with the units the floor holds; and `InstIneq` forces the unit `N`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT TT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem tt_fine_extent {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (μ : Fin 3) :
    scaleUp 2 1 Lu μ + 1 = 120 := by
  rw [scaleUp_succ 2 1 Lu (by norm_num) μ, hLu μ]; norm_num

/-- the hypotheses of `closed_point_proper_cond` other than the units, at `TT`, with a nonzero class element and `Omega_0 != torus` -/
theorem tt_hypotheses {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    (∀ μ : Fin 3, 4 ≤ Lu μ) ∧ (∀ μ, 2 ∣ Lu μ + 1) ∧ 3 ≤ 6 * 2 ∧
    Admissible 2 2 6 1 (TT (scaleUp 2 1 Lu)) ∧ LambdaOK2 2 2 6 1 (TT (scaleUp 2 1 Lu)) (LamT Lu) ∧
    (∃ p : PeriodicLatticeSite (scaleUp 2 1 Lu), p ∉ (TT (scaleUp 2 1 Lu)).Om 0) ∧
    (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (LamT Lu) 2 Bt ∧ OnLambdaT (LamT Lu) Bt ∧ 0 < bondEnergy Bt) := by
  have hLf := tt_fine_extent hLu
  obtain ⟨-, hadm, -, -, -, hnot, hLam, -, -, hB⟩ :=
    proper_tower_hyps (Lf := scaleUp 2 1 Lu) hLu hLf (α₀ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨fun μ => by have := hLu μ; omega, fun μ => by rw [hLu μ]; norm_num, by norm_num, hadm, hLam, hnot, hB⟩

theorem tt_floor_conditional {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hell : 0 < 2)
    (a : ℝ) (ha : 0 < a)
    (hG : IsUnit (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)).G1inv)
    (hN : IsUnit (GenP.Nmat (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)))) :
    InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg := by
  obtain ⟨h4, hd, hRM, hadm, hLam, -, -⟩ := tt_hypotheses hLu
  exact closed_point_proper_cond h4 hd hRM hell a ha _ hadm _ hLam hG hN

theorem tt_instIneq_iff_unit {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hell : 0 < 2)
    (a : ℝ) (ha : 0 < a) :
    (IsUnit (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)).G1inv ∧
      IsUnit (GenP.Nmat (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu))) →
        InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg) ∧
    (InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg →
      IsUnit (GenP.Nmat (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)))) := by
  refine ⟨fun h => tt_floor_conditional hLu hell a ha h.1 h.2, fun hI => ?_⟩
  obtain ⟨-, -, -, -, -, -, hB⟩ := tt_hypotheses hLu
  exact unit_N_of_instIneq hell a (1 / 1728) ha (by norm_num) _ _ hI hB

#print axioms tt_hypotheses
#print axioms tt_floor_conditional
#print axioms tt_instIneq_iff_unit

end AdalyFormal.DirichletMono
