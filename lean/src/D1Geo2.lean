import D1Geo1

/-!
# D1Geo2 -- `R D* A = 0` for the single-bond field at the boundary bond: hence `T A = 0` and `W A = A`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-- `D* (X δ_{(x,0)})` is supported on `{x, x + e₀}`. -/
theorem gradAdj_sing_supp (U : Cfg L) (x : PeriodicLatticeSite L) (X : SuTwo) (z : PeriodicLatticeSite L)
    (hz1 : z ≠ x) (hz2 : z ≠ periodicLatticeShift x 0) : (gradAdj U (sing (x, (0 : Fin 3)) X)) z = 0 := by
  rw [show (gradAdj U (sing (x, (0 : Fin 3)) X)) z = (WithLp.ofLp (gradAdj U (sing (x, (0 : Fin 3)) X))) z from rfl,
    gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h1 : (sing (x, (0 : Fin 3)) X) (z, μ) = 0 := sing_apply_ne _ _ (fun h => hz1 (Prod.mk.inj h).1)
  have h2 : (sing (x, (0 : Fin 3)) X) (periodicLatticeShiftBack z μ, μ) = 0 := by
    refine sing_apply_ne _ _ (fun h => ?_)
    obtain ⟨ha, hb⟩ := Prod.mk.inj h
    apply hz2
    subst hb
    rw [← ha, periodicLatticeShift_shiftBack]
  have h1' : (WithLp.ofLp (sing (x, (0 : Fin 3)) X)) (z, μ) = 0 := h1
  have h2' : (WithLp.ofLp (sing (x, (0 : Fin 3)) X)) (periodicLatticeShiftBack z μ, μ) = 0 := h2
  rw [h1', h2']
  simp

theorem Tfull_sing_zero {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hRM : 3 ≤ R * M)
    {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x) (U : Cfg L) (X : SuTwo) :
    Tfull (geomOf ell k S) U (sing (x, (0 : Fin 3)) X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : z = x ∨ z = periodicLatticeShift x 0
  · have hu0 : u z = 0 := by
      refine RImage_support S U hu z (fun y hy hy1 => ?_)
      have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) (periodicLatticeShift x 0) hbd.hx' y hy1
      have hp : pdist z y ≤ 1 := hy
      have hzx : pdist (periodicLatticeShift x 0) z ≤ 1 := by
        rcases hz with rfl | rfl
        · rw [pdist_comm]; exact pdist_shift_le _ _
        · rw [AdalyFormal.StatementLaneR8.pdist_self]; omega
      have := pdist_triangle (periodicLatticeShift x 0) z y
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hcl
      omega
    rw [show u z = 0 from hu0]
    simp
  · push_neg at hz
    rw [gradAdj_sing_supp U x X z hz.1 hz.2]
    simp

theorem Wop_sing {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hRM : 3 ≤ R * M)
    {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x) (U : Cfg L) (a : ℝ) (X : SuTwo) :
    Wop (geomOf ell k S) U a (sing (x, (0 : Fin 3)) X) = sing (x, (0 : Fin 3)) X := by
  have hT := Tfull_sing_zero hS hRM hbd U X
  unfold Tfull at hT
  simp only [ContinuousLinearMap.comp_apply] at hT
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [hT]
  simp

#print axioms Tfull_sing_zero
#print axioms Wop_sing

end AdalyFormal.D1Literal
