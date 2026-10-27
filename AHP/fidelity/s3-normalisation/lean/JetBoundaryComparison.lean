import ZXR2Sector

set_option autoImplicit false

namespace AdalyFormal.AHP.FidelS3Normalisation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

theorem raw_level_zero
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) :
    C2rawB G U 0 A = 0 := by
  rw [C2rawB_eq, C2CompL_zero, map_zero]

theorem linear_level_zero
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) :
    QlinB G U 0 A = A := by
  exact QlinB_zero G U A

theorem plainH_eq_uniformBody_at_depth_one
    {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (A : BondFnL2 L) (j : ℕ) (hj : j ≤ 1) :
    (((G.ell : ℝ)⁻¹) ^ 2) • C2rawB G U j A =
      (G.ell : ℝ)⁻¹ •
        ((((G.ell : ℝ) ^ j)⁻¹) • C2rawB G U j A) := by
  have h : j = 0 ∨ j = 1 := by omega
  rcases h with rfl | rfl
  · simp only [raw_level_zero, smul_zero]
  · simp only [pow_one, pow_two, mul_smul]

end AdalyFormal.AHP.FidelS3Normalisation

#print axioms AdalyFormal.AHP.FidelS3Normalisation.raw_level_zero
#print axioms AdalyFormal.AHP.FidelS3Normalisation.linear_level_zero
#print axioms AdalyFormal.AHP.FidelS3Normalisation.plainH_eq_uniformBody_at_depth_one
