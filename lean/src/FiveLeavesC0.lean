/- Audit C0 repair only. Same existential claim as the submitted draft; not raw-5 or SI1. -/
import RawUbarDerivNoLoop
import L4AuditCompletion

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.LeavesAuditC0

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open OneStep124 (gInvOp adOp)
open AdalySI1.ModifiedAverageDeriv (configMul)

/-- **C0 (log token → `gInvOp`), mechanical composition of two already-paid theorems.**
For every block point `x`, the derivative of `t ↦ su2Log (loopVar ...)` at `0` is the
`gInvOp`-image of the packaged raw-leg `SuTwo` value `Vloop x * (loopVar 1 ell V0' c x)⁻¹`,
`Vloop x` being the derivative of the SU2-coerced loop curve itself (the paid `hasDerivAt_
loopVar_configMul` four-term value, not re-transcribed here). This is `hasDerivAt_su2Log_gInvOp`
instantiated at `hasDerivAt_loopVar_configMul`; no new mathematics. -/
theorem hasDerivAt_su2Log_loopVar_gInvOp
    {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hnc2 : loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x ≠ su2NegOne) :
    ∃ (V : M2) (hW : HasDerivAt
        (fun t : ℝ => ((loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2))
        V 0),
      HasDerivAt
        (fun t : ℝ => su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x))
        (gInvOp (-(adOp (principalSuTwoLog
              (loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x))))
            (⟨V * Ring.inverse
                ((loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x : SU2) : M2),
              AdalySI1.L4Audit.rightTrivialized_mem_suTwo
                (W := fun t : ℝ => loopVar 1 ell
                  (configMul (fun e => su2Exp (t • A e)) V0) c x) (V := V) hW hnc2⟩ : SuTwo) : M2) 0 := by
  have hW := AdalySI1.RawUbarDerivNoLoop.hasDerivAt_loopVar_configMul V0 A hah htr ell c x
  refine ⟨_, hW, ?_⟩
  exact AdalySI1.L4Audit.hasDerivAt_su2Log_gInvOp
    (W := fun t : ℝ => loopVar 1 ell
      (configMul (fun e => su2Exp (t • A e)) V0) c x) hW hnc2

#print axioms hasDerivAt_su2Log_loopVar_gInvOp

end AdalySI1.LeavesAuditC0
