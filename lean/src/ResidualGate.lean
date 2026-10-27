import SourcePrecision
set_option autoImplicit false
set_option maxRecDepth 10000
namespace HConstruction.SNFRepair
open HConstruction.SmallNF HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

theorem twoSidedInverse_iff_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (T : E →L[ℝ] E) :
    (∃ G : E →L[ℝ] E, (∀ x, T (G x) = x) ∧ (∀ x, G (T x) = x)) ↔
      Function.Injective T := by
  constructor
  · rintro ⟨G,_,hG⟩ x y h
    calc
      x = G (T x) := (hG x).symm
      _ = G (T y) := congrArg G h
      _ = y := hG y
  · intro hi
    let e : E ≃L[ℝ] E := (LinearEquiv.ofBijective T.toLinearMap
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
    exact ⟨e.symm.toContinuousLinearMap, e.apply_symm_apply, e.symm_apply_apply⟩

/-- A reformulation of the OPEN physical inverse obligation, not a discharge. -/
theorem physicalG0_iff_injective (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ) :
    HasPhysicalG0 U a ↔ Function.Injective (precisionU U a) :=
  twoSidedInverse_iff_injective (precisionU U a)

/-- A genuine residual certificate would suffice. No matrix approximation is
silently identified with the operator in this statement. -/
theorem physicalG0_iff_residual (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ) :
    HasPhysicalG0 U a ↔ ∃ N : H →L[ℝ] H,
      ‖ContinuousLinearMap.id ℝ H - N.comp (precisionU U a)‖ < 1 := by
  constructor
  · rintro ⟨N,_,hN⟩
    refine ⟨N, ?_⟩
    have heq : ContinuousLinearMap.id ℝ H - N.comp (precisionU U a) = 0 := by
      ext x
      simp only [sub_apply,ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply,hN,sub_self,zero_apply]
    rw [heq,norm_zero]
    norm_num
  · rintro ⟨N,hN⟩
    apply (physicalG0_iff_injective U a).mpr
    intro x y hxy
    have hz : precisionU U a (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    let E := ContinuousLinearMap.id ℝ H - N.comp (precisionU U a)
    have he : E (x-y) = x-y := by simp [E,hz]
    have hb := E.le_opNorm (x-y)
    rw [he] at hb
    have hn : ‖x-y‖ = 0 := by
      by_contra hn
      have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      have hlt := mul_lt_mul_of_pos_right hN hp
      dsimp [E] at hb
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- This criterion is exact, but neither side is asserted by this theorem. -/
theorem chosen_inverse_gate : HasPhysicalG0 chosenU 1 ↔
    ∃ N : H →L[ℝ] H, ‖ContinuousLinearMap.id ℝ H - N.comp chosenPrecision‖ < 1 :=
  physicalG0_iff_residual chosenU 1

/-- The requested inverse is not nonunique if it exists. -/
theorem physicalG0_unique (U : PeriodicLinkConfiguration SU2 witnessL) (a : ℝ)
    (G N : H →L[ℝ] H)
    (hG : ∀ A, G (precisionU U a A) = A)
    (hN : ∀ A, precisionU U a (N A) = A) : G = N := by
  ext A
  calc
    G A = G (precisionU U a (N A)) := congrArg G (hN A).symm
    _ = N A := hG (N A)
end HConstruction.SNFRepair
