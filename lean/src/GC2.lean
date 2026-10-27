import GC1
import ZLocOps

/-!
# GC2 -- operator-level gauge covariance of `D_U`-curl and of `Δ_P = D*χ_P D + Δ'_P` (any plaquette set `P`).
`adB γ f = (b ↦ R(γ b₋) f b)` is a linear isometric bijection of `BondFnL2 L`;
`deltaKLocCLM (U^γ) P ∘ adB γ = adB γ ∘ deltaKLocCLM U P`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply curlValueCovariant_gauge gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent}

/-- `Ad_γ` on `L²` bond fields. -/
def adB (γ : GaugeFn L) : BondFnL2 L →ₗ[ℝ] BondFnL2 L where
  toFun f := WithLp.toLp 2 (gaugeActA γ (WithLp.ofLp f))
  map_add' f g := by
    ext b; simp [gaugeActA_apply]
  map_smul' c f := by
    ext b; simp [gaugeActA_apply]

theorem adB_apply (γ : GaugeFn L) (f : BondFnL2 L) (b : Bond L) :
    (adB γ f) b = RMap (γ b.1) (f b) := rfl

theorem inner_adB (γ : GaugeFn L) (x y : BondFnL2 L) : ⟪adB γ x, adB γ y⟫ = ⟪x, y⟫ := by
  simp only [PiLp.inner_apply, adB_apply]
  exact Finset.sum_congr rfl (fun b _ => AdalyFormal.Balaban.SuTwoInner.inner_RMap _ _ _)

theorem adB_inv (γ : GaugeFn L) (x : BondFnL2 L) : adB (gaugeInv γ) (adB γ x) = x := by
  ext b
  simp only [adB_apply, RMap_mul_apply, gaugeInv, inv_mul_cancel, RMap_one]
  rfl

theorem adB_surj (γ : GaugeFn L) : Function.Surjective (adB γ) := by
  intro y
  refine ⟨adB (gaugeInv γ) y, ?_⟩
  have := adB_inv (gaugeInv γ) y
  have h2 : gaugeInv (gaugeInv γ) = γ := by funext x; simp [gaugeInv]
  rwa [h2] at this

/-- operator identity from the form identity (any inner-preserving surjection). -/
theorem op_of_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, ⟪A x, A y⟫ = ⟪x, y⟫) (hs : Function.Surjective A) (T T' : E →L[ℝ] E)
    (h : ∀ x y, ⟪A x, T' (A y)⟫ = ⟪x, T y⟫) (y : E) : T' (A y) = A (T y) := by
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨x, rfl⟩ := hs v
  rw [h, hA]

/-- covariant curl on `L²`, pointwise. -/
theorem curlL2_apply (U : PeriodicLinkConfiguration SU2g L) (x : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    (curlCovariantLM_L2 U x) p = AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U (WithLp.ofLp x) p := rfl

theorem curlL2_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L) (x : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    (curlCovariantLM_L2 (periodicGaugeTransform γ U) (adB γ x)) p
      = RMap (γ p.1) ((curlCovariantLM_L2 U x) p) := by
  rw [curlL2_apply, curlL2_apply]
  exact curlValueCovariant_gauge γ U (WithLp.ofLp x) p

theorem plaq_form_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ⟪plaqMask P (curlCovariantLM_L2 (periodicGaugeTransform γ U) (adB γ x)),
      plaqMask P (curlCovariantLM_L2 (periodicGaugeTransform γ U) (adB γ y))⟫
    = ⟪plaqMask P (curlCovariantLM_L2 U x), plaqMask P (curlCovariantLM_L2 U y)⟫ := by
  simp only [PiLp.inner_apply, plaqMask_apply, curlL2_gauge]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · exact AdalyFormal.Balaban.SuTwoInner.inner_RMap _ _ _
  · simp

theorem rawLoc_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilRawLoc (periodicGaugeTransform γ U) P (gaugeActA γ A) (gaugeActA γ B)
      = deltaPrimeBilRawLoc U P A B := by
  rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · exact bilPlaq_gauge γ U p A B
  · rfl

theorem bil_form_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc (periodicGaugeTransform γ U) P (adB γ x) (adB γ y)
      = deltaPrimeBilL2NormLoc U P x y := by
  show deltaPrimeBilNormLoc (periodicGaugeTransform γ U) P (gaugeActA γ (WithLp.ofLp x))
      (gaugeActA γ (WithLp.ofLp y)) = deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [rawLoc_gauge, rawLoc_gauge]

theorem form_gauge_Delta (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ⟪adB γ x, deltaKLocCLM (periodicGaugeTransform γ U) P (adB γ y)⟫ = ⟪x, deltaKLocCLM U P y⟫ := by
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM, plaq_form_gauge, bil_form_gauge]

/-- **`Δ_P(U^γ) = Ad_γ Δ_P(U) Ad_γ⁻¹`**, every `P`, every `γ`, every `U`. -/
theorem deltaKLocCLM_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (P : Set (PeriodicLatticePlaquette L)) (y : BondFnL2 L) :
    deltaKLocCLM (periodicGaugeTransform γ U) P (adB γ y) = adB γ (deltaKLocCLM U P y) :=
  op_of_form (adB γ) (inner_adB γ) (adB_surj γ) _ _ (form_gauge_Delta γ U P) y

#print axioms inner_adB
#print axioms adB_surj
#print axioms plaq_form_gauge
#print axioms bil_form_gauge
#print axioms deltaKLocCLM_gauge

end AdalyFormal.GaugeCov
