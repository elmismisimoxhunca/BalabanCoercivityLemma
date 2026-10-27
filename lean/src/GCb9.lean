import GCb8
import ZT5A

/-!
# GCb9 -- the hypotheses and the support conditions of the inner claim are gauge-invariant
* `ClassCoupled` (per-cube existential gauge) is invariant under `U ↦ U^γ` (and conversely);
* `OnLambdaTildeIn`, `OnLambdaT`, `OnLambda` are invariant under `B̃ ↦ B̃^g` (supports are pointwise);
* `bondEnergy` is invariant (`bondEnergy_gauge`, tree).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv gaugeTransform_inv bondEnergy_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

variable {L : PeriodicLatticeExtent}

theorem classCoupled_gauge {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) (γ : GaugeFn L) :
    ClassCoupled ell M c k S α₀ η (periodicGaugeTransform γ U) :=
  ⟨h.1, perCubeRegular2_gauge h.2 γ⟩

theorem classCoupled_gauge_iff {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (γ : GaugeFn L) :
    ClassCoupled ell M c k S α₀ η (periodicGaugeTransform γ U) ↔ ClassCoupled ell M c k S α₀ η U := by
  constructor
  · intro h
    have := classCoupled_gauge h (gaugeInv γ)
    rwa [gaugeTransform_inv] at this
  · intro h; exact classCoupled_gauge h γ

theorem gaugeActA_eq_zero_iff' {Lu : PeriodicLatticeExtent} (g : GaugeFn Lu) (B : Bond Lu → SuTwo) (b : Bond Lu) :
    gaugeActA g B b = 0 ↔ B b = 0 := by
  rw [gaugeActA_apply]
  constructor
  · intro h
    have := AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap (g b.1) (B b)
    rw [h, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  · intro h; rw [h, map_zero]

theorem onLambdaT_gauge {Lu : PeriodicLatticeExtent} (g : GaugeFn Lu) (Lam : Set (PeriodicLatticeSite Lu))
    (B : Bond Lu → SuTwo) : OnLambdaT Lam (gaugeActA g B) ↔ OnLambdaT Lam B := by
  unfold OnLambdaT
  exact forall_congr' (fun b => imp_congr_right (fun _ => gaugeActA_eq_zero_iff' g B b))

theorem onLambda_gauge {Lu : PeriodicLatticeExtent} (g : GaugeFn Lu) (Lam : Set (PeriodicLatticeSite Lu))
    (B : Bond Lu → SuTwo) : OnLambda Lam (gaugeActA g B) ↔ OnLambda Lam B := by
  unfold OnLambda
  exact forall_congr' (fun b => imp_congr_right (fun _ => gaugeActA_eq_zero_iff' g B b))

theorem onLambdaTildeIn_gauge {Lu : PeriodicLatticeExtent} (g : GaugeFn Lu) (Lam : Set (PeriodicLatticeSite Lu))
    (ell : ℕ) (B : Bond Lu → SuTwo) : OnLambdaTildeIn Lam ell (gaugeActA g B) ↔ OnLambdaTildeIn Lam ell B := by
  unfold OnLambdaTildeIn
  refine and_congr ?_ ?_
  · exact forall_congr' (fun y => imp_congr_right (fun _ => forall_congr' (fun x => imp_congr_right (fun _ =>
      forall_congr' (fun b => imp_congr_right (fun _ => gaugeActA_eq_zero_iff' g B b))))))
  · exact forall_congr' (fun b => imp_congr_right (fun _ => gaugeActA_eq_zero_iff' g B b))

#print axioms classCoupled_gauge
#print axioms classCoupled_gauge_iff
#print axioms onLambdaTildeIn_gauge

end AdalyFormal.GaugeCov
