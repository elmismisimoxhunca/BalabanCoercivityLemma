/-
Audit-owned analytic-slot continuation. These equalities concern ONLY the exp-of-mean-log
slot, not the entire modified derivative and not any single CMP98 channel. The four loop
legs, blocked-frame adjoint and seven-to-five assembly remain separate obligations.
-/
import L4AuditCompletion
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section
namespace AdalySI1.DexpSumAudit
open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open OneStep124 (gOp gInvOp adOp)

/-- Distribute the identified exponential differential through an arbitrary finite weighted sum. -/
theorem dexp_sum_apply {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Z : SuTwo) (D : ι → SuTwo) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2))
        (∑ i ∈ s, w i • (D i : M2)) * NormedSpace.exp (-(Z : M2)) =
      ((∑ i ∈ s, w i • gOp (-(adOp Z)) (D i) : SuTwo) : M2) := by
  have h := AdalySI1.DexpRodrigues.dexp_eq_gOp Z (∑ i ∈ s, w i • D i)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] using h

/-- Replace the literal log derivatives inside that slot using the unconditional off-cut L4
clause. Arbitrary real weights and arbitrary SuTwo exp basepoint; identity loops allowed. -/
theorem dexp_sum_log_deriv {ι : Type*} (s : Finset ι) (w : ι → ℝ) (Z : SuTwo)
    (W : ι → ℝ → SU2) (V : ι → M2)
    (hW : ∀ i, HasDerivAt (fun t => ((W i t : SU2) : M2)) (V i) 0)
    (hne : ∀ i, W i 0 ≠ su2NegOne) :
    (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z : M2))
        (∑ i ∈ s, w i • deriv (fun t => su2Log (W i t)) 0)
        * NormedSpace.exp (-(Z : M2)) =
      ((∑ i ∈ s, w i • gOp (-(adOp Z))
        (gInvOp (-(adOp (principalSuTwoLog (W i 0))))
          (⟨V i * Ring.inverse ((W i 0 : SU2) : M2),
            AdalySI1.L4Audit.rightTrivialized_mem_suTwo (hW i) (hne i)⟩ : SuTwo)) : SuTwo) : M2) := by
  let D : ι → SuTwo := fun i => gInvOp (-(adOp (principalSuTwoLog (W i 0))))
    ⟨V i * Ring.inverse ((W i 0 : SU2) : M2),
      AdalySI1.L4Audit.rightTrivialized_mem_suTwo (hW i) (hne i)⟩
  have hD : ∀ i, deriv (fun t => su2Log (W i t)) 0 = (D i : M2) := fun i =>
    (AdalySI1.L4Audit.hasDerivAt_su2Log_gInvOp (hW i) (hne i)).deriv
  simp_rw [hD]
  exact dexp_sum_apply s w Z D

#print axioms dexp_sum_apply
#print axioms dexp_sum_log_deriv
run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.DexpSumAudit.dexp_sum_apply,
      `AdalySI1.DexpSumAudit.dexp_sum_log_deriv] do
    unless (← Lean.getEnv).contains name do throwError "Missing theorem: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do throwError "Nonstandard axiom in {name}: {ax}"
  Lean.logInfo "DEXP_SUM_AUDIT_STANDARD_AXIOMS_PASS"
end AdalySI1.DexpSumAudit
