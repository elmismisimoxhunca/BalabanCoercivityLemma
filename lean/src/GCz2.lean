import GCz1

/-!
# GCz2 -- the inner claim's conclusion is gauge invariant: `genC` covariant, `WellDefG` invariant, `InstIneq`/`InstAtWD` transfer.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv gaugeTransform_inv bondEnergy_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- `T' ∘ A = A ∘ T` for an isometric equivalence `A`: `T'` is a unit iff `T` is. -/
theorem isUnit_intertwine {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (A : X ≃ₗᵢ[ℝ] X) {T T' : X →L[ℝ] X} (h : ∀ x, T' (A x) = A (T x)) : IsUnit T' ↔ IsUnit T := by
  let Ac : X ≃L[ℝ] X := A.toContinuousLinearEquiv
  let φ := Ac.conjContinuousAlgEquiv
  have hφ : T' = φ T := by
    ext1 z
    have := h (A.symm z)
    rw [A.apply_symm_apply] at this
    simp only [Ac, φ, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    exact this
  rw [hφ]
  constructor
  · intro hu
    have := hu.map φ.symm.toAlgEquiv.toRingEquiv.toRingHom.toMonoidHom
    simpa using this
  · intro hu
    exact hu.map φ.toAlgEquiv.toRingEquiv.toRingHom.toMonoidHom

/-- the hypothesis bundle of `GCg4`, discharged for `U' = U^γ`. -/
theorem genFormHyps_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) :
    GenFormHyps P (periodicGaugeTransform γ P.U) γ :=
  ⟨bondEqv_gauge P γ, fun B' => D2in_gauge P (periodicGaugeTransform γ P.U) (uOf P.ell P.k P.Lu P.hell γ)
    (fun B c => Q1_gauge_pt P γ B c) (fun B c => C2tilde_gauge_pt P γ B c) B'⟩

/-- `C` of (3.157) is gauge covariant. -/
theorem genC_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) (Bt : Bond P.Lu → SuTwo) :
    GenP.genC (gaugeP P γ) (gaugeActA (uOf P.ell P.k P.Lu P.hell γ) Bt)
      = gaugeActA (uOf P.ell P.k P.Lu P.hell γ) (GenP.genC P Bt) :=
  Cop_gauge (fun B c => Q1_gauge_pt P γ B c) Bt

#print axioms genFormHyps_gauge
#print axioms genC_gauge

end AdalyFormal.GaugeCov
