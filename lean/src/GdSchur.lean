import GdFam

/-!
# GdSchur -- `Q G Q*` is a unit when `Ginv` is a unit that is positive on `ker Q` and `Q*` is injective (generic), and its use on the twist family.
The two hypotheses `hQs`, `hpos` are NOT proved here for the NV-slab twist family (see LOG round 3): `hpos` is the statement that the compression of `Ginv(θ)` to `ker Q` is positive.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

section generic
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Schur step: `M` a symmetric unit, positive on `ker Q`, `Q*` injective  ⟹  `Q M⁻¹ Q*` is a unit (no definiteness of `M` on all of `E` needed). -/
theorem isUnit_Q_inv_Qs_of_pos_ker {M : E →L[ℝ] E} (hsym : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (hM : IsUnit M)
    {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E} (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hQs : Function.Injective Qs)
    (hpos : ∀ x, Q x = 0 → x ≠ 0 → 0 < ⟪x, M x⟫) :
    IsUnit ((Q.comp (Ring.inverse M)).comp Qs) := by
  obtain ⟨u, hu'⟩ := hM
  have hG1 : Ring.inverse M = ↑u⁻¹ := by rw [← hu', Ring.inverse_unit]
  have hl : ∀ x, M (Ring.inverse M x) = x := fun x => by
    rw [hG1, ← hu']
    exact ContinuousLinearMap.ext_iff.mp u.mul_inv x
  have hinj : Function.Injective ((Q.comp (Ring.inverse M)).comp Qs) := by
    rw [injective_iff_map_eq_zero]
    intro lam0 h0
    simp only [ContinuousLinearMap.comp_apply] at h0
    set x := Ring.inverse M (Qs lam0) with hx
    have hQx : Q x = 0 := h0
    have hMx : M x = Qs lam0 := hl _
    by_contra hne
    have hz : Qs lam0 ≠ 0 := fun h => hne (hQs (by simpa using h))
    have hxne : x ≠ 0 := fun h => hz (by rw [← hMx, h]; simp)
    have := hpos x hQx hxne
    rw [hMx, ← hQ, hQx, inner_zero_left] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (show F →ₗ[ℝ] F from (Q.comp (Ring.inverse M)).comp Qs))).mp hinj⟩

end generic

variable (sD sJ : PlaqSel) (P : IngrBParams)

/-- on the twist family, `GapAt` holds as soon as `Q*` is injective and `Ginv` is positive on `ker Q` (whenever `Ginv` is a unit). -/
theorem GapAt_theta_of_pos_ker {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M) (θ : ℝ)
    (hU : P.U = Uth (P.S.Om 0) θ)
    (hQs : Function.Injective (dataS sD sJ P).Qs)
    (hpos : ∀ A, (dataS sD sJ P).Q A = 0 → A ≠ 0 → 0 < ⟪A, (dataS sD sJ P).Ginv A⟫) :
    GapAt sD sJ P := by
  rw [GapAt_theta_iff sD sJ P hS hell h3 θ hU]
  intro hu
  exact isUnit_Q_inv_Qs_of_pos_ker ((dataS sD sJ P).Ginv_symm (dataS_laws sD sJ P)) hu (dataS sD sJ P).Q_adj hQs hpos

#print axioms isUnit_Q_inv_Qs_of_pos_ker
#print axioms GapAt_theta_of_pos_ker

end AdalyFormal.D1Guarded
