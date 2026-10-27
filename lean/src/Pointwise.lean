import InverseGate
set_option autoImplicit false
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.LineIntegralAveraging

/-- The actual native q124 in value coordinates, all 192 input bonds. -/
theorem nativeQ_pointwise (A : H) (c : CoarseBond witnessL (1 * 2)) :
    cfl2Equiv 2 (nativeLinearQ (trivialU witnessL) 2 A) c =
      (1/16 : ℝ) • ∑ x ∈ blockOf c.1.1 2,
        (bfl2Equiv A (x,c.2) + bfl2Equiv A (periodicLatticeShift x c.2,c.2)) := by
  change AdalyFormal.DeltaKR85.q124Principal 1 2 (trivialU witnessL)
    (fineCoordinates A) c = _
  rw [q124_flat]
  unfold AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov
  simp only [mem_coarseLattice_one, dif_pos, Nat.mul_one,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply, Finset.sum_range_succ, Finset.sum_range_zero,
    pathSite_zero, pathSite_succ, zero_add]
  norm_num only [Nat.cast_ofNat, one_div, pow_succ, pow_zero, mul_one]
  congr 1
  apply Finset.sum_bij (fun u _ => u.1)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu v hv h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x,mem_coarseLattice_one x⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  · intro u hu
    rfl

noncomputable def constBond (c : Fin 3 → SuTwo) : H := bfl2Equiv.symm (fun b => c b.2)

lemma nativeQ_const (v : Fin 3 → SuTwo) (c : CoarseBond witnessL (1 * 2)) :
    cfl2Equiv 2 (nativeLinearQ (trivialU witnessL) 2 (constBond v)) c = v c.2 := by
  rw [nativeQ_pointwise]
  simp only [constBond, LinearEquiv.apply_symm_apply, Finset.sum_const]
  have hc : (blockOf c.1.1 2).card = 8 := by
    exact card_blockOf_of_coarse (by intro μ; exact ⟨2,rfl⟩) c.1.2
  rw [hc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  module

/-- Eta^{-1}=2 cancels the length-average 1/2: the native derivative commutes
with the SITE Q' and the physical unit coarse gradient, not with the wrong Q. -/
lemma nativeQ_grad (f : S) (c : CoarseBond witnessL (1 * 2)) :
    cfl2Equiv 2 (nativeLinearQ (trivialU witnessL) 2 (flatGrad f)) c =
      coarseRestrictSiteCovariant 2 (fiberEquiv _ f) (coarseShift c.1.1 2 c.2) -
      coarseRestrictSiteCovariant 2 (fiberEquiv _ f) c.1.1 := by
  rw [nativeQ_pointwise]
  have hg (x : PeriodicLatticeSite witnessL) : bfl2Equiv (flatGrad f) (x,c.2) =
      (2 : ℝ) • ((fiberEquiv _ f) (periodicLatticeShift x c.2) - (fiberEquiv _ f) x) := by
    simp [flatGrad, gradCovariantLM, gradValueCovariant, trivialU, RMap_one]
  simp only [hg]
  have hstep (x : PeriodicLatticeSite witnessL) :
      (2 : ℝ) • (fiberEquiv _ f (periodicLatticeShift x c.2) - fiberEquiv _ f x) +
      (2 : ℝ) • (fiberEquiv _ f (periodicLatticeShift (periodicLatticeShift x c.2) c.2) -
        fiberEquiv _ f (periodicLatticeShift x c.2)) =
      (2 : ℝ) • (fiberEquiv _ f (coarseShift x 2 c.2) - fiberEquiv _ f x) := by
    change (2 : ℝ) • (_ - _) + (2 : ℝ) • (_ - _) = (2 : ℝ) •
      (fiberEquiv _ f (periodicLatticeShift (periodicLatticeShift x c.2) c.2) - fiberEquiv _ f x)
    module
  simp only [hstep, ← Finset.smul_sum, smul_smul]
  have hreindex : (∑ x ∈ blockOf (coarseShift c.1.1 2 c.2) 2, fiberEquiv _ f x) =
      ∑ x ∈ blockOf c.1.1 2, fiberEquiv _ f (coarseShift x 2 c.2) := by
    rw [AdalyFormal.Balaban.CoarseShiftCovariance.coarseShift_blockOf_eq_image
      (by decide : 0 < 2) (show 2 ∣ witnessL c.2 + 1 from ⟨2,rfl⟩) c.1.2]
    exact Finset.sum_image fun x _ x' _ h =>
      AdalyFormal.Balaban.CoarseShiftCovariance.coarseShift_injective 2 c.2 h
  simp only [coarseRestrictSiteCovariant]
  rw [hreindex, Finset.sum_sub_distrib]
  module
end HConstruction.DRepair
