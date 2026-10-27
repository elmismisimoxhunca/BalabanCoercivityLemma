import LastLayer
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap_one)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.QcEquation (blockCorner)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open Reproduced (stepLift)

/-- Every length-two segment in an aligned block has exactly one last-layer
hit, and that hit belongs to this very block. Ordinary finite proof, no oracle. -/
lemma hit_geometry : ∀ (c : CoarseBond witnessL (1 * 2))
    (u : {z : PeriodicLatticeSite witnessL // z ∈ CoarseLattice witnessL 1}),
    u ∈ unitSitesOf 1 2 c.1.1 →
    (((u.1 c.2).val % 2 = 1 ∧ blockCorner 2 u.1 = c.1.1 ∧
      ¬ ((pathSite u.1 c.2 1 c.2).val % 2 = 1)) ∨
     (¬ ((u.1 c.2).val % 2 = 1) ∧ (pathSite u.1 c.2 1 c.2).val % 2 = 1 ∧
      blockCorner 2 (pathSite u.1 c.2 1) = c.1.1)) := by
  intro c u hu
  have hx : u.1 ∈ blockOf c.1.1 2 := (Finset.mem_filter.mp hu).2
  have hc := AdalyFormal.Balaban.QcEquation.blockCorner_of_mem_blockOf c.1.2 hx
  have hs := AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val u.1 c.2 1
  have hlt : (u.1 c.2).val < 4 := (u.1 c.2).isLt
  change (pathSite u.1 c.2 1 c.2).val = ((u.1 c.2).val + 1) % 4 at hs
  by_cases h0 : (u.1 c.2).val % 2 = 1
  · exact Or.inl ⟨h0, hc, by omega⟩
  · refine Or.inr ⟨h0, by omega, ?_⟩
    apply AdalyFormal.Balaban.QcEquation.blockCorner_of_mem_blockOf c.1.2
    apply mem_blockOf.mpr
    intro ν
    by_cases hν : ν = c.2
    · subst ν
      have hb := mem_blockOf.mp hx c.2
      have hy0 := mem_CoarseLattice.mp c.1.2 c.2
      change (c.1.1 c.2).val % 2 = 0 at hy0
      constructor <;> omega
    · rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ _ _ _ hν]
      exact mem_blockOf.mp hx ν

lemma lift_line (B : CoarseBond witnessL (1 * 2) → SuTwo)
    (c : CoarseBond witnessL (1 * 2))
    (u : {z : PeriodicLatticeSite witnessL // z ∈ CoarseLattice witnessL 1})
    (hu : u ∈ unitSitesOf 1 2 c.1.1) :
    stepLift 1 2 B (u,c.2) +
      stepLift 1 2 B (⟨pathSite u.1 c.2 1, mem_coarseLattice_one _⟩,c.2) =
      (2 : ℝ) • B c := by
  have he (x : PeriodicLatticeSite witnessL) (hx : blockCorner 2 x = c.1.1) :
      (⟨blockCorner 2 x, AdalyFormal.Balaban.QcEquation.blockCorner_mem x⟩,
        c.2) = c := by
    apply Prod.ext
    · exact Subtype.ext hx
    · rfl
  rcases hit_geometry c u hu with ⟨h0,hc,h1⟩ | ⟨h0,h1,hc⟩
  · simp only [stepLift, Nat.one_mul, show 2 - 1 = 1 from rfl,
      if_pos h0, if_neg h1, add_zero]
    rw [he u.1 hc]
    norm_num
  · simp only [stepLift, Nat.one_mul, show 2 - 1 = 1 from rfl,
      if_neg h0, if_pos h1, zero_add]
    rw [he _ hc]
    norm_num

/-- Exact right inverse for the actual certified first jet, not a surrogate Q. -/
theorem q124_stepLift (B : CoarseBond witnessL (1 * 2) → SuTwo)
    (c : CoarseBond witnessL (1 * 2)) :
    AdalyFormal.DeltaKR85.q124Principal 1 2 (trivialU witnessL)
      (stepLift 1 2 B) c = B c := by
  rw [q124_flat]
  unfold AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov
  simp only [mem_coarseLattice_one, dif_pos, Nat.mul_one,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, LinearMap.id_apply]
  have hl : ∀ u ∈ unitSitesOf 1 2 c.1.1,
      (∑ i ∈ Finset.range 2,
        stepLift 1 2 B (⟨pathSite u.1 c.2 i, mem_coarseLattice_one _⟩,c.2)) =
        (2 : ℝ) • B c := by
    intro u hu
    simpa [Finset.sum_range_succ, AdalyFormal.Balaban.QOne.pathSite_zero]
      using lift_line B c u hu
  rw [Finset.sum_congr rfl hl, Finset.sum_const, card_all c,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  norm_num

/-- Algebraic last-layer section ONLY. It is not claimed to minimize the
physical energy, and is not substituted for solutionOperator. -/
noncomputable def nativeSection : CFL2 witnessL 2 →L[ℝ] H :=
  LinearMap.toContinuousLinearMap (fineCoordinates.symm.toLinearMap.comp
    (({ toFun := stepLift 1 2
        map_add' := fun x y => funext (Reproduced.stepLift_add 1 2 x y)
        map_smul' := fun r x => funext (Reproduced.stepLift_smul 1 2 r x) } :
       (CoarseBond witnessL (1 * 2) → SuTwo) →ₗ[ℝ] (CoarseBond witnessL 1 → SuTwo)).comp
      (cfl2Equiv 2).toLinearMap))

theorem nativeLinearQ_section (B : CFL2 witnessL 2) :
    nativeLinearQ (trivialU witnessL) 2 (nativeSection B) = B := by
  apply (cfl2Equiv 2).injective
  funext c
  change AdalyFormal.DeltaKR85.q124Principal 1 2 (trivialU witnessL)
    (fineCoordinates (nativeSection B)) c = cfl2Equiv 2 B c
  have he : fineCoordinates (nativeSection B) = stepLift 1 2 (cfl2Equiv 2 B) :=
    fineCoordinates.apply_symm_apply _
  rw [he]
  exact q124_stepLift _ c

theorem nativeLinearQ_surjective : Function.Surjective (nativeLinearQ (trivialU witnessL) 2) :=
  fun B => ⟨nativeSection B, nativeLinearQ_section B⟩

end HConstruction.DRepair
