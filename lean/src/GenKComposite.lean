import GenKMinimum
import DK3FineFlatQ
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.TowerLawCov (tower_law_cov_at_trivial)
open AdalySI1.Multiscale (qCompositeBond qCompositeBond_succ)
open HConstruction.Carrier (fineCoordinates)
variable {L : PeriodicLatticeExtent}

/-- The previously hand-unfolded depth-two/depth-three bridge is now one
induction, with divisibility paid at every factor. It covers all k. -/
theorem composite_flat_line (k : ℕ) (hd : ∀ μ : Fin 3, 2^k ∣ L μ+1) (A : BFL2 L) :
    qCompositeBond (fun _ => trivialU L) 2 k (fineCoordinates A) =
      lineCoarseRestrictCovLM (trivialU L) (2^k) (bfl2Equiv A) := by
  induction k with
  | zero =>
    funext c
    change fineCoordinates A c = lineCoarseRestrictCov (trivialU L) 1 (bfl2Equiv A) c
    rw [lineCoarseRestrictCov_trivialU]
    simp only [lineCoarseRestrictSuTwo,AdalyFormal.Balaban.FourierFaithfulU1.blockOf_one,
      Finset.sum_singleton,Finset.sum_range_succ,Finset.sum_range_zero,
      AdalyFormal.Balaban.QOne.pathSite_zero,zero_add,Nat.cast_one,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_smul]
    rfl
  | succ k ih =>
    have hd0 : ∀ μ : Fin 3, 2^k ∣ L μ+1 := fun μ =>
      dvd_trans (dvd_mul_right (2^k) 2) (by simpa only [pow_succ] using hd μ)
    change AdalyFormal.DeltaKR85.q124Principal (2^k) 2 (trivialU L)
      (qCompositeBond (fun _ => trivialU L) 2 k (fineCoordinates A)) =
      lineCoarseRestrictCovLM (trivialU L) ((2^k)*2) (bfl2Equiv A)
    rw [ih hd0]
    funext c
    rw [HConstruction.DK3.FineScale.FlatQ.q124_flat (2^k) (pow_pos (by decide) k)
      (fun μ => by simpa only [pow_succ] using hd μ)]
    exact congrFun (tower_law_cov_at_trivial (pow_pos (by decide : 0<2) k)
      (by decide : 0<2) hd0 (bfl2Equiv A)) c

/-- The generic incoming map is literally the certified ordered qCompositeBond,
reindexed on the unit torus; no new averaging convention. -/
theorem incoming_composite (M : PeriodicLatticeExtent) (k : ℕ)
    (A : Fine M (n := 2^k)) (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond M) :
    bfl2Equiv (incoming M (pow_pos (by decide : 0<2) k) A) b =
      qCompositeBond (fun _ => trivialU (fineExtent M (2^k))) 2 k (fineCoordinates A)
        (bonds M (pow_pos (by decide : 0<2) k) b) := by
  rw [composite_flat_line k (fineTiling M (pow_pos (by decide : 0<2) k)) A]
  rfl

/-- Equality to the independently certified Hermitian-chart source Q_j. -/
theorem incoming_source (M : PeriodicLatticeExtent) (k : ℕ)
    (A : Fine M (n := 2^k)) (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond M) :
    bfl2Equiv (incoming M (pow_pos (by decide : 0<2) k) A) b =
      AdalyQIdentification.QJ.QjInChart (fun _ => trivialU (fineExtent M (2^k))) 2 k
        (fineCoordinates A) (bonds M (pow_pos (by decide : 0<2) k) b) := by
  rw [AdalyQIdentification.QJ.QjInChart_eq_qCompositeBond]
  exact incoming_composite M k A b

#print axioms incoming_source
#print axioms composite_flat_line
#print axioms incoming_composite
end HConstruction.GenK
