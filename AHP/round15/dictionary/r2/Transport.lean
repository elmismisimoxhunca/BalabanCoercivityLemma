import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
variable {L : PeriodicLatticeExtent}
example (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A B : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P A B =
      deltaPrimeBilNormLoc U P (WithLp.ofLp A) (WithLp.ofLp B) := by
  rfl
example (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A B : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P A B =
      deltaPrimeBilNormLoc U P (WithLp.ofLp A) (WithLp.ofLp B) := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl,
    show B = WithLp.toLp 2 (WithLp.ofLp B) from rfl]
  rfl

namespace Test
open AdalyFormal.D1Literal
example {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) (A B : BondFnL2 L)
    (e : Bond L) (X : SuTwo) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg L) P (sing e X) A =
      deltaPrimeBilNormLoc (flatCfg : Cfg L) P
        (WithLp.ofLp (sing e X)) (WithLp.ofLp A) := by
  rfl
example {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) (A B : BondFnL2 L)
    (e : Bond L) (X : SuTwo) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg L) P (sing e X) A =
      deltaPrimeBilNormLoc (flatCfg : Cfg L) P
        (WithLp.ofLp (sing e X)) (WithLp.ofLp A) := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl]
  rfl
example {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) (A B : BondFnL2 L)
    (e : Bond L) (X : SuTwo)
    (hraw1 : deltaPrimeBilRawLoc (flatCfg : Cfg L) P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
      deltaPrimeBilRawLoc (flatCfg : Cfg L) P (WithLp.ofLp (sing e X)) (WithLp.ofLp B))
    (hraw2 : deltaPrimeBilRawLoc (flatCfg : Cfg L) P (WithLp.ofLp A) (WithLp.ofLp (sing e X)) =
      deltaPrimeBilRawLoc (flatCfg : Cfg L) P (WithLp.ofLp B) (WithLp.ofLp (sing e X))) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg L) P (sing e X) A =
      deltaPrimeBilL2NormLoc (flatCfg : Cfg L) P (sing e X) B := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl,
    show B = WithLp.toLp 2 (WithLp.ofLp B) from rfl]
  show deltaPrimeBilNormLoc (flatCfg : Cfg L) P
    (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
    deltaPrimeBilNormLoc (flatCfg : Cfg L) P
      (WithLp.ofLp (sing e X)) (WithLp.ofLp B)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [hraw1, hraw2]
  ring
#check AdalyFormal.CoverOmega.Qfull_flat_row
#check AdalyFormal.CoverOmega.bgTower_flat
#check AdalyFormal.GenuineU1.Qcomp_closed
#check AdalyFormal.GenuineU1.suCoordFInv_suCoordF
#check AdalyFormal.IngredientFamilyR2.QlinCompL_eq_QlinCompX
#check AdalyFormal.Balaban.UbarTowerCov.Ubar_flat
#check AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo
#check AdalyFormal.M1IMS.row_aligned
#check AdalyFormal.IngredientFamilyR2.Ubar_flat
#check AdalyFormal.IngredientFamilyR2.suCoordFInv_suCoordF
#check Sigma.ext
#check Sigma.ext_iff
#check Sigma.mk.injEq
#check AdalyFormal.Balaban.RegularityGap.shiftBack_ne_self
#check AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self
open AdalyFormal.Balaban.CovariantHjMinimizer
example {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    x = periodicLatticeShift x μ ∨ x = periodicLatticeShiftBack (periodicLatticeShift x μ) μ := by
  right
  exact (periodicLatticeShiftBack_shift _ _).symm
example {L : PeriodicLatticeExtent} (A : BondFnL2 L) (e : Bond L) (X : SuTwo) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg L) Set.univ (sing e X) A =
      deltaPrimeBilNormLoc (flatCfg : Cfg L) Set.univ
        (WithLp.ofLp (sing e X)) (WithLp.ofLp A) := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl]
  rfl
example {L : PeriodicLatticeExtent} (A : BondFnL2 L) (e : Bond L) (X : SuTwo) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg L) Set.univ (sing e X) A = 0 := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl]
  exact deltaPrimeBilNormLoc_trivialU (L := L) Set.univ
    (WithLp.ofLp (sing e X)) (WithLp.ofLp A)
end Test
