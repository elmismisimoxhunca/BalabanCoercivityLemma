import DK3FlatAverage
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3
open HConstruction.Carrier HConstruction.Predicate
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf staircasePath)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap_one)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
attribute [local irreducible] blockOf CoarseLattice staircasePath

abbrev K := BFL2 unitL
abbrev W := CFL2 unitL 2
def unitCoordinates : K ≃ₗ[ℝ] (Bond unitL → SuTwo) := bfl2Equiv

def unitInput : K →L[ℝ] Fine unitL := fineCoordinates.toLinearMap.toContinuousLinearMap

theorem unitInput_apply (B : K) (b : CoarseBond unitL 1) :
    unitInput B b = unitCoordinates B (b.1.1,b.2) := rfl

theorem unit_even : ∀ μ : Fin 3, 2 ∣ (unitL μ + 1) := tiling.2

/-- Raw eta=1 normalization of Q1 on T^(3); its kernel is the normalized Q1 kernel. -/
def nativeRawQ (t : ℝ) : K →L[ℝ] W := LinearMap.toContinuousLinearMap
  ((cfl2Equiv (L := unitL) 2).symm.toLinearMap.comp
    ((unitQ1 t).comp ((2:ℝ) • unitInput.toLinearMap)))

def rawLinear : K →L[ℝ] W := nativeRawQ 0

def axialSpace : Submodule ℝ K where
  carrier := {B | ∀ y ∈ CoarseLattice unitL 2, ∀ x ∈ blockOf y 2,
    ∀ b ∈ staircasePath y x, unitCoordinates B b = 0}
  zero_mem' := by simp
  add_mem' := by intro B C hB hC y hy x hx b hb; simp [hB y hy x hx b hb,hC y hy x hx b hb]
  smul_mem' := by intro r B hB y hy x hx b hb; simp [hB y hy x hx b hb]

private theorem sum_unit {E : Type*} [AddCommMonoid E] (m : ℕ) (y : US)
    (f : US → E) : (∑ u ∈ unitSitesOf 1 m y, f u.1) = ∑ x ∈ blockOf y m, f x := by
  rw [← unitSitesOf_one_image_eq_blockOf y m,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  simp only [one_mul]

theorem rawLinear_sum (B : K) (c : CoarseBond unitL (1*2)) :
    cfl2Equiv 2 (rawLinear B) c = (1/8 : ℝ) • ∑ x ∈ blockOf c.1.1 2,
      (unitCoordinates B (x,c.2) + unitCoordinates B (periodicLatticeShift x c.2,c.2)) := by
  change AdalyFormal.DeltaKR85.q124Principal 1 2 (V 0) ((2:ℝ) • unitInput B) c = _
  rw [V_zero, GeneralAverage.q124_flat unit_even]
  unfold AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov
  simp only [mem_coarseLattice_one, dif_pos, Nat.mul_one,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply, Finset.sum_range_succ, Finset.sum_range_zero,
    pathSite_zero, pathSite_succ, zero_add, Pi.smul_apply, unitInput_apply]
  norm_num only [Nat.cast_ofNat, one_div, pow_succ, pow_zero, mul_one]
  rw [sum_unit 2 c.1.1
    (fun x => (2:ℝ) • unitCoordinates B (x,c.2) +
      (2:ℝ) • unitCoordinates B (periodicLatticeShift x c.2,c.2))]
  simp only [← smul_add, ← Finset.smul_sum, smul_smul]
  norm_num
end HConstruction.DK3
