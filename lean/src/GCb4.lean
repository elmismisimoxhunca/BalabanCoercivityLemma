import GCb3

/-!
# GCb4 -- `Ring.inverse` conjugation, `G'`, `W = I - D G' R D*`, `T = R D*` equivariant under `Ad_γ`
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `Ring.inverse` commutes with conjugation by an isometric equivalence (unit and non-unit case). -/
theorem ringInverse_eqv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E ≃ₗᵢ[ℝ] E) (T T' : E →L[ℝ] E) (h : ∀ x, T' (A x) = A (T x)) (x : E) :
    Ring.inverse T' (A x) = A (Ring.inverse T x) := by
  let Ac : E ≃L[ℝ] E := A.toContinuousLinearEquiv
  let φ := Ac.conjContinuousAlgEquiv
  have hφ : T' = φ T := by
    ext1 z
    have := h (A.symm z)
    rw [A.apply_symm_apply] at this
    simp only [Ac, φ, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    exact this
  have hφx : ∀ S : E →L[ℝ] E, φ S (A x) = A (S x) := by
    intro S
    simp only [φ, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    show Ac (S (Ac.symm (Ac x))) = A (S x)
    simp [Ac]
  by_cases hT : IsUnit T
  · obtain ⟨u, rfl⟩ := hT
    have : Ring.inverse T' = φ (Ring.inverse (u : E →L[ℝ] E)) := by
      have e : φ (u : E →L[ℝ] E) = ((Units.map φ.toAlgEquiv.toRingEquiv.toRingHom.toMonoidHom u : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) := rfl
      rw [hφ, e, Ring.inverse_unit, Ring.inverse_unit, ← map_inv]
      rfl
    rw [this, hφx]
  · have h1 : Ring.inverse T = 0 := Ring.inverse_non_unit _ hT
    have h2 : ¬ IsUnit T' := by
      intro hu
      apply hT
      have : T = φ.symm T' := by rw [hφ]; simp
      rw [this]
      exact hu.map φ.symm.toAlgHom.toRingHom.toMonoidHom
    rw [h1, Ring.inverse_non_unit _ h2]
    simp

end AdalyFormal.GaugeCov
