import B0i

/-!
# W1 -- non-vacuity of the `RegTower` hypothesis of `B0_fullTower` (and hence of GN5/GN8), at `U ≠ 1`

* `ubarTower_trivial`: the background tower of `trivialU` is `trivialU` at every level.
* `regTower_pureGauge`: for EVERY gauge `g` (any SU(2)-valued site function), `U = (trivialU)^g` has
  `RegTower ell (UbarTower su2LogExp ell U) J` for every `J` (all averaging loops are conjugates of `1`).
  These `U` are genuinely `≠ 1` for non-constant `g` (they are pure gauge, curvature zero).
* `B0_pureGauge`: `B0_fullTower` applies to all of them (its hypothesis is satisfiable, not vacuous).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Log_one su2Exp_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_succ UbarTower_zero UbarTower_gauge loopVar
  loopVar_gauge stridedBlockedGauge coarseBondVar gammaVarStrided)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy_trivialU)
open AdalyFormal.StatementLane (scaleUp)

variable {L : PeriodicLatticeExtent}

theorem loopVar_trivial (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    loopVar s ell (trivialU L) c x = 1 := by
  simp [loopVar, gammaVarStrided, coarseBondVar, coarsePathHolonomy_trivialU]

theorem ubarTower_trivial (ell : ℕ) (j : ℕ) : UbarTower su2LogExp ell (trivialU L) j = trivialU L := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [UbarTower_succ, ih]
      funext c
      simp [stridedBlockedGauge, loopVar_trivial, coarseBondVar, coarsePathHolonomy_trivialU]
      rfl

theorem regTower_pureGauge (ell J : ℕ) (g : PeriodicLatticeSite L → SU2) :
    RegTower ell (UbarTower su2LogExp ell (periodicGaugeTransform g (trivialU L))) J := by
  intro j _ c x hx
  rw [UbarTower_gauge, ubarTower_trivial, loopVar_gauge _ _ _ _ _ hx, loopVar_trivial]
  have h1 : (1 : M2) ∈ LogReg := mem_of_mem_nhds LogReg_mem_nhds_one
  simpa using h1

theorem B0_pureGauge (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → SU2) :
    ∀ ν ∈ NQp (geomOf ell k (fullTower ell k Lu)) (periodicGaugeTransform g (trivialU _)),
      (bondSectorOf (geomOf ell k (fullTower ell k Lu)) (periodicGaugeTransform g (trivialU _))).Qfull
        (gradL2 (periodicGaugeTransform g (trivialU _)) ν) = 0 :=
  B0_fullTower ell k Lu hell _ (regTower_pureGauge ell k g)

#print axioms loopVar_trivial
#print axioms ubarTower_trivial
#print axioms regTower_pureGauge
#print axioms B0_pureGauge

end AdalyFormal.SliceCoerc
