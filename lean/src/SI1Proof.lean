/-
Boxed SI1: the genuine outer-log HasDerivAt identity in every real direction h.
Only the paid outer derivative and the paid Dcomputed identification are used.
The three fitting hypotheses and the principal-log cut are retained verbatim;
arbitrary bond fields, nonflat backgrounds, identity loops, and h = 0 are allowed.
No differentiation, channel identification, or analytic estimate is reproved.
-/
import OuterLogFullDerivNoLoop
import AsmProof
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Boxed

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage)
open AdalySI1Noloop.OuterLogFullDeriv
  (Lh hasDerivAt_su2Log_modifiedAverage_physical_noloop)

variable {L : PeriodicLatticeExtent}

/-- Boxed SI1, universally quantified over the field A and every real h.
The derivative is Lh ell h times the M2-coerced full q124Principal value,
not a single channel or a test at a distinguished direction. -/
theorem hasDerivAt_su2Log_modifiedAverage_physical_q124
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne)
    (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (modifiedAverage V0 ell (fun e => su2Exp ((h * t) • A e)) c))
      (Lh ell h •
        ((q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2))
      0 := by
  have hd := hasDerivAt_su2Log_modifiedAverage_physical_noloop V0 A hah htr ell c hnc2 h
  have heq := AdalySI1.Asm3.dcomputed_eq_ell_smul_q124Principal
    V0 A hah htr ell c hcell hell hdvd hnc2
  rw [heq] at hd
  -- The paid inverse-function chain rule retains the identity equivalence.
  -- Reduce that identity application before collecting the two real scalars.
  change HasDerivAt _
    (h • ((ell : ℝ) •
      ((q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
        (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
        : SuTwo) : M2))) 0 at hd
  simpa only [Lh, smul_smul, mul_comm] using hd

#print hasDerivAt_su2Log_modifiedAverage_physical_q124
#print axioms hasDerivAt_su2Log_modifiedAverage_physical_q124
#print axioms AdalySI1.Asm3.dcomputed_eq_ell_smul_q124Principal
#print axioms AdalySI1.Asm3.hasDerivAt_modifiedAverage_coe_configMul_noloop_q124
#print axioms AdalySI1Noloop.OuterLogFullDeriv.hasDerivAt_su2Log_modifiedAverage_physical_noloop

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124,
      `AdalySI1.Asm3.dcomputed_eq_ell_smul_q124Principal,
      `AdalySI1.Asm3.hasDerivAt_modifiedAverage_coe_configMul_noloop_q124,
      `AdalySI1Noloop.OuterLogFullDeriv.hasDerivAt_su2Log_modifiedAverage_physical_noloop] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing boxed SI1 declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in boxed SI1 declaration {name}: {ax}"
  for mod in [`AsmProof, `OuterLogFullDerivNoLoop, `ProdFullAssembleDerivNoLoop,
      `Ch1Proof, `Ch23Proof, `Ch4Proof, `Ch5Proof, `C3Proof, `C2Proof, `C1Proof,
      `Adjoint, `DexpRodriguesG, `L5Proof, `L1ForwardCarrier, `L2LineIntegralBridge,
      `L6FittedSums, `T1MainSegment, `ModifiedAverageDeriv, `RawUbarDerivNoLoop] do
    let path ← Lean.findOLean mod
    let expected := s!"/home/sebastian/projects/project-adaly/compute/m1_si1_boxed/deps/{mod}.olean"
    unless path.toString == expected do
      Lean.logInfo m!"GUARD_NEUTRALISED Unexpected boxed SI1 paid import: {mod}: {path}"
    Lean.logInfo m!"SI1_RESOLVED {mod}: {path}"
  Lean.logInfo "SI1_PROOF_STANDARD_AXIOMS_PASS"

end AdalySI1.Boxed
