/-
Audit-owned continuation. Derive surjectivity of g(-ad log g) from the paid off-cut
log derivatives along exp(t v) g; finite dimension then gives the unit. This does
not import the spectral ladder or assume invertibility. Identity is included.
-/
import L4
import L7
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalySI1.L4Audit
open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne su2Log_one
  su2Log_antiHermitian su2Log_traceless su2Exp_coe_of_antiHerm_traceless coe_mul coe_one)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo)
open AdalyFormal.Balaban.RegularityGap (su2_exp_log_of_ne_negOne)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open OneStep124 (gOp gInvOp adOp)

/-- Eliminate the explicit log-differentiability premise, including W(0)=1. -/
theorem log_differentiable {W : ℝ → SU2} {V : M2}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne) : DifferentiableAt ℝ (fun t => su2Log (W t)) 0 := by
  by_cases h1 : W 0 = 1
  · exact (AdalySI1.RawUbarDerivNoLoop.hasDerivAt_su2Log_su2_curve_at_one 0 hW h1).differentiableAt
  · exact (AdalySI1.RawAverageDeriv.hasDerivAt_su2Log_su2_curve 0 hW h1 hne rfl).differentiableAt

theorem exp_principalLog {g : SU2} (hne : g ≠ su2NegOne) :
    NormedSpace.exp ((principalSuTwoLog g : SuTwo) : M2) = (g : M2) := by
  change NormedSpace.exp (su2Log g) = _
  rw [← su2Exp_coe_of_antiHerm_traceless (su2Log_antiHermitian g) (su2Log_traceless g),
    su2_exp_log_of_ne_negOne g hne]

/-- The forward exp/log chain rule, with no inverse hypothesis. -/
theorem forward_log_derivative {W : ℝ → SU2} {V : M2} {D : SuTwo}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne)
    (hD : HasDerivAt (fun t => su2Log (W t)) (D : M2) 0) :
    ((gOp (-(adOp (principalSuTwoLog (W 0)))) D : SuTwo) : M2)
      = V * Ring.inverse ((W 0 : SU2) : M2) := by
  let Z : SuTwo := principalSuTwoLog (W 0)
  have hfd : HasFDerivAt (NormedSpace.exp : M2 → M2)
      (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (Z : M2) :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (Z : M2)).differentiableAt.hasFDerivAt
  have hc := hfd.comp_hasDerivAt_of_eq (0 : ℝ) hD (by rfl)
  have hneM : ((W 0 : SU2) : M2) ≠ ((su2NegOne : SU2) : M2) :=
    fun h => hne (Subtype.ext h)
  have hevent := hW.continuousAt.eventually_ne hneM
  have heq : (fun t : ℝ => ((W t : SU2) : M2)) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ => NormedSpace.exp (su2Log (W t))) := by
    filter_upwards [hevent] with t ht
    exact (exp_principalLog (fun h => ht (congrArg Subtype.val h))).symm
  have hcW : HasDerivAt (fun t => ((W t : SU2) : M2))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2)) (D : M2)) 0 :=
    hc.congr_of_eventuallyEq heq
  have hV := hcW.unique hW
  have hexpneg : NormedSpace.exp (-(Z : M2)) = Ring.inverse ((W 0 : SU2) : M2) := by
    rw [← exp_principalLog hne]
    exact (Ring.inverse_exp (Z : M2)).symm
  have h := (AdalySI1.DexpRodrigues.dexp_eq_gOp Z D).symm
  rw [hV, hexpneg] at h
  exact h

/-- General off-cut invertibility, obtained without a spectral import. -/
theorem gOp_principalLog_isUnit {g : SU2} (hne : g ≠ su2NegOne) :
    IsUnit (gOp (-(adOp (principalSuTwoLog g)))) := by
  let T := gOp (-(adOp (principalSuTwoLog g)))
  have hsurj : Function.Surjective T := by
    intro v
    let W : ℝ → SU2 := fun t => su2Exp (t • (v : M2)) * g
    have h0 : W 0 = g := by simp [W]
    have he := AdalySI1.IngredientDeriv.hasDerivAt_su2Exp_coe_smul v.2.1 v.2.2
    let R : M2 →L[ℝ] M2 := (ContinuousLinearMap.mul ℝ M2).flip (g : M2)
    have hr := R.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) he rfl
    have hW : HasDerivAt (fun t => ((W t : SU2) : M2)) ((v : M2) * (g : M2)) 0 :=
      hr.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => coe_mul _ _))
    have hcut : W 0 ≠ su2NegOne := by rwa [h0]
    have hd := (log_differentiable hW hcut).hasDerivAt
    let D : SuTwo := ⟨deriv (fun t => su2Log (W t)) 0,
      AdalySI1.L7.mem_suTwo_of_hasDerivAt hd
        (fun t => ⟨su2Log_antiHermitian (W t), su2Log_traceless (W t)⟩)⟩
    refine ⟨D, ?_⟩
    apply Subtype.coe_injective
    have hkey := forward_log_derivative hW hcut (D := D) hd
    rw [h0] at hkey
    have hgunit : IsUnit (g : M2) := by
      rw [← exp_principalLog hne]
      exact NormedSpace.isUnit_exp _
    exact hkey.trans (Ring.mul_inverse_cancel_right (g : M2) (v : M2) hgunit)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨(LinearMap.injective_iff_surjective (f := T.toLinearMap)).mpr hsurj, hsurj⟩

/-- L4's actual derivative-value equality: hD and hunit are discharged. -/
theorem deriv_su2Log_eq_gInvOp {W : ℝ → SU2} {V : M2}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne)
    (v : SuTwo) (hv : (v : M2) = V * Ring.inverse ((W 0 : SU2) : M2)) :
    deriv (fun t => su2Log (W t)) 0 =
      ((gInvOp (-(adOp (principalSuTwoLog (W 0)))) v : SuTwo) : M2) :=
  AdalySI1.L4.su2Log_deriv_eq_gInvOp hW hne (log_differentiable hW hne).hasDerivAt
    v hv (gOp_principalLog_isUnit hne)

/-- The right-trivialized matrix tangent is in suTwo; no carrier hypothesis is assumed. -/
theorem rightTrivialized_mem_suTwo {W : ℝ → SU2} {V : M2}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne) : V * Ring.inverse ((W 0 : SU2) : M2) ∈ suTwo := by
  have hd := (log_differentiable hW hne).hasDerivAt
  let D : SuTwo := ⟨deriv (fun t => su2Log (W t)) 0,
    AdalySI1.L7.mem_suTwo_of_hasDerivAt hd
      (fun t => ⟨su2Log_antiHermitian (W t), su2Log_traceless (W t)⟩)⟩
  rw [← forward_log_derivative hW hne (D := D) hd]
  exact (gOp (-(adOp (principalSuTwoLog (W 0)))) D).2

/-- The complete principal-log derivative clause, with only the curve derivative and off-cut
hypothesis. In particular neither identity exclusion, hD, hunit nor tangent membership is owed. -/
theorem hasDerivAt_su2Log_gInvOp {W : ℝ → SU2} {V : M2}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne) :
    HasDerivAt (fun t => su2Log (W t))
      ((gInvOp (-(adOp (principalSuTwoLog (W 0))))
        (⟨V * Ring.inverse ((W 0 : SU2) : M2), rightTrivialized_mem_suTwo hW hne⟩ : SuTwo)
          : SuTwo) : M2) 0 := by
  rw [← deriv_su2Log_eq_gInvOp hW hne _ rfl]
  exact (log_differentiable hW hne).hasDerivAt

theorem gInvOp_mul_gOp_principalLog {g : SU2} (hne : g ≠ su2NegOne) :
    gInvOp (-(adOp (principalSuTwoLog g))) * gOp (-(adOp (principalSuTwoLog g))) = 1 :=
  Ring.inverse_mul_cancel _ (gOp_principalLog_isUnit hne)

theorem gOp_mul_gInvOp_principalLog {g : SU2} (hne : g ≠ su2NegOne) :
    gOp (-(adOp (principalSuTwoLog g))) * gInvOp (-(adOp (principalSuTwoLog g))) = 1 :=
  Ring.mul_inverse_cancel _ (gOp_principalLog_isUnit hne)

#print axioms log_differentiable
#print axioms forward_log_derivative
#print axioms gOp_principalLog_isUnit
#print axioms deriv_su2Log_eq_gInvOp
#print axioms rightTrivialized_mem_suTwo
#print axioms hasDerivAt_su2Log_gInvOp
#print axioms gInvOp_mul_gOp_principalLog
#print axioms gOp_mul_gInvOp_principalLog

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.L4Audit.log_differentiable,
      `AdalySI1.L4Audit.forward_log_derivative,
      `AdalySI1.L4Audit.gOp_principalLog_isUnit,
      `AdalySI1.L4Audit.deriv_su2Log_eq_gInvOp,
      `AdalySI1.L4Audit.rightTrivialized_mem_suTwo,
      `AdalySI1.L4Audit.hasDerivAt_su2Log_gInvOp,
      `AdalySI1.L4Audit.gInvOp_mul_gOp_principalLog,
      `AdalySI1.L4Audit.gOp_mul_gInvOp_principalLog] do
    unless (← Lean.getEnv).contains name do throwError "Missing theorem: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do throwError "Nonstandard axiom in {name}: {ax}"
  Lean.logInfo "L4_AUDIT_STANDARD_AXIOMS_PASS"
end AdalySI1.L4Audit
