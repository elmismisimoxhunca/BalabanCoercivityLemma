import MC1

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2

theorem fullTower_classCube (ell M c k : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (Lu : PeriodicLatticeExtent) (z : PeriodicLatticeSite (scaleUp ell k Lu))
    (hz : GridCorner (bigSide M ell k) z) :
    IsClassCube ell M c k (fullTower ell k Lu)
      (siteBox z (c * bigSide M ell k)) k := by
  have hsz : 0 < c * bigSide M ell k := by
    simp only [bigSide]; exact Nat.mul_pos hc (Nat.mul_pos hM (pow_pos hell k))
  have hB : ∀ i, i < k → towerBj (fullTower ell k Lu) i = ∅ := by
    intro i hi
    have h1 : i ≤ k := by omega
    have h2 : i + 1 ≤ k := by omega
    ext y
    simp [towerBj, fullTower, h1, h2]
  have hBk : towerBj (fullTower ell k Lu) k = Set.univ := by
    ext y
    simp [towerBj, fullTower]
  have hnon : (siteBox z (c * bigSide M ell k) ∩ towerBj (fullTower ell k Lu) k).Nonempty := by
    refine ⟨z, ?_, by rw [hBk]; exact Set.mem_univ _⟩
    intro μ
    have : (z μ).val + (scaleUp ell k Lu μ + 1) - (z μ).val = scaleUp ell k Lu μ + 1 := by omega
    rw [this, Nat.mod_self]; exact hsz
  refine ⟨⟨le_refl k, ⟨z, hz, rfl⟩, ?_, hnon⟩, ?_⟩
  · intro y _; left; rw [hBk]; exact Set.mem_univ _
  · intro i hi
    by_contra hne
    have hlt : i < k := lt_of_le_of_ne hi.1 hne
    obtain ⟨y, _, hy⟩ := hi.2.2.2
    rw [hB i hlt] at hy
    exact hy

theorem gridBelow_corner {L : PeriodicLatticeExtent} (s : ℕ) (x : PeriodicLatticeSite L) :
    GridCorner s (gridBelow s x) := by
  intro μ
  simp only [gridBelow]
  exact Nat.mul_mod_left _ _

/-- **`fullTower_coversp` for a GENERAL torus**: every site and every plaquette lies in a class cube of factor `c ≥ 2`
(torus tiled by `M`). -/
theorem fullTower_coversp (ell M c k : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 2 ≤ c)
    (Lu : PeriodicLatticeExtent) (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) :
    CoversOm0p ell M c k (fullTower ell k Lu) := by
  have hs : 0 < bigSide M ell k := by simp only [bigSide]; exact Nat.mul_pos hM (pow_pos hell k)
  have hd : ∀ ρ : Fin 3, bigSide M ell k ∣ scaleUp ell k Lu ρ + 1 := by
    intro ρ
    rw [scaleUp_succ ell k Lu hell ρ]
    simp only [bigSide]
    rw [mul_comm M]
    exact (Nat.mul_dvd_mul_left (ell ^ k) (hT ρ)).trans (by rw [mul_comm])
  have cube : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
      IsClassCube ell M c k (fullTower ell k Lu) (siteBox (gridBelow (bigSide M ell k) x) (c * bigSide M ell k)) k :=
    fun x => fullTower_classCube ell M c k hell hM (by omega) Lu _ (gridBelow_corner _ x)
  constructor
  · intro x _
    exact ⟨_, k, cube x, near_mem_box _ c hs hc hd x x (near_self x)⟩
  · intro p _
    obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
    have hne : μ ≠ ν := ne_of_lt hμν
    refine ⟨_, k, cube x, ?_⟩
    have mem := fun y (hy : Near x y) => near_mem_box _ c hs hc hd x y hy
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨mem _ (near_self x), mem _ (near_shift_first x μ)⟩
    · exact ⟨mem _ (near_shift_first x μ), mem _ (near_shift_second x μ ν hne)⟩
    · exact ⟨mem _ (near_shift_first x ν), mem _ (near_shift_second x ν μ hne.symm)⟩
    · exact ⟨mem _ (near_self x), mem _ (near_shift_first x ν)⟩

#print axioms fullTower_admissible
#print axioms univ_lambdaOK2
#print axioms fullTower_coversp
#print axioms near_mem_box

end AdalyFormal.M0Corollary
