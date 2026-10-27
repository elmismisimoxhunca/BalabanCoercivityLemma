/-
C2 CONTRACT ONLY: executable proposition, NOT a proof of C2.
Owned directory: compute/m1_si1_c2_gated/spec/.
Read-only paid roots: ../deps/FiveLeavesC0, ../deps/C1Proof, and ../deps/Adjoint.

The definition below freezes the literal pointwise log derivative and its four
separate contributions. It does not prove the equality. In particular, this
file does not assume derivative-witness uniqueness, the packaged tangent
identity, principal-log exp/log recovery, or P_x Ad_{W_x} = N_x.
-/
import FiveLeavesC0
import C1Proof
import Adjoint
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C2Contract

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gInvOp)

variable {L : PeriodicLatticeExtent}

/-- UNPROVED C2 equality at one literal loop site.

Dictionary, all at `V0`, stride `1`:
* `q = coarseGammaPath 1 c.1 x`;
* `p = coarsePathHolonomy 1 V0 c.1 q`;
* `K = ubarSU2 1 ell V0 c`;
* `W = loopVar 1 ell V0 c x`;
* `Zx = principalSuTwoLog W`;
* `Z` is the raw weighted bracket packaged as `SuTwo`;
* `tau`, `sigma`, `phi`, and `d` are the literal near, shifted-segment,
  raw far-path, and direct-path line-integral leaves.

The negative far and negative direct leaves are distinct. No fitting,
positivity, nonzero-log, flatness, gradient-direction, support, or
identity-loop exclusion is present in this equality. -/
def C2Point (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : Prop :=
  let q : List (Fin 3) := coarseGammaPath 1 c.1 x
  let r : List (Fin 3) := List.replicate ell c.2
  let p : SU2 := coarsePathHolonomy 1 V0 c.1 q
  let K : SU2 := ubarSU2 1 ell V0 c
  let W : SU2 := loopVar 1 ell V0 c x
  let Zx : SuTwo := principalSuTwoLog W
  let Z : SuTwo := ⟨ubarBracket V0 ell c,
    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
  let Aunit := fineDirToUnitBond A hah htr
  let tauSu : SuTwo := lineIntegral 1 V0 Aunit c.1 q
  let sigmaSu : SuTwo := RMap p (lineIntegral 1 V0 Aunit x r)
  let phiSu : SuTwo := lineIntegral 1 V0 Aunit (cPlusS 1 ell c) q
  let dSu : SuTwo := lineIntegral 1 V0 Aunit c.1 r
  deriv (fun t : ℝ =>
      su2Log (loopVar 1 ell
        (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0
    = ((gInvOp (-(adOp Zx)) tauSu
        + gInvOp (-(adOp Zx)) sigmaSu
        - gInvOp (adOp Zx) (expOp (-(adOp Z)) (RMap K phiSu))
        - gInvOp (adOp Zx) dSu : SuTwo) : M2)

/-- THE SINGLE ACCEPTANCE TARGET (UNPROVED).

C2 quantifies over an arbitrary lattice extent, nonflat background, and
anti-Hermitian traceless matrix field. The carrier premise is the literal
`stepBlockOf` membership. The only additional analytic premise is the pointwise
principal-log cut `W_x ≠ -I`; identity loops remain allowed.

A future proof must derive, rather than assume, the literal log derivative,
uniqueness of C0's loop-derivative witness, equality of the packaged tangent by
`Subtype.ext`, and the paid-B consequence `P_x Ad_{W_x} = N_x`. -/
def C2Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L),
    x ∈ stepBlockOf c.1 1 ell →
    loopVar 1 ell V0 c x ≠ su2NegOne →
    C2Point V0 A hah htr ell c x

/-
Future proof-owner interface (SIGNATURE ONLY; no theorem with this name exists here):

  theorem AdalySI1.C2Proof.su2Log_loopVar_deriv_eq_log4 :
    AdalySI1.C2Contract.C2Target

A proposition definition that elaborates is not a proof. The future theorem must
inhabit this exact target and pass the separate acceptance template.
-/

#print C2Point
#print C2Target
#print axioms C2Point
#print axioms C2Target

-- Fresh existence/axiom receipts for the exact paid declarations named by the contract.
#print axioms AdalySI1.LeavesAuditC0.hasDerivAt_su2Log_loopVar_gInvOp
#print axioms AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent
#print axioms AdalySI1.C1Proof.near_dict
#print axioms AdalySI1.C1Proof.literal_deriv_frame
#print axioms AdalySI1.C1Proof.loopVar_rightTrivialized_eq_four_legs
#print axioms AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad
#print axioms AdalySI1.Adjoint.gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad
#print axioms AdalySI1.RawUbarDerivNoLoop.configMul_zero_eq
#print axioms AdalySI1.RawUbarDerivNoLoop.loopVar_configMul_zero
#print axioms AdalySI1.L4Audit.rightTrivialized_mem_suTwo
#print axioms AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.LeavesAuditC0.hasDerivAt_su2Log_loopVar_gInvOp,
      `AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent,
      `AdalySI1.C1Proof.near_dict,
      `AdalySI1.C1Proof.literal_deriv_frame,
      `AdalySI1.C1Proof.loopVar_rightTrivialized_eq_four_legs,
      `AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad,
      `AdalySI1.Adjoint.gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad,
      `AdalySI1.RawUbarDerivNoLoop.configMul_zero_eq,
      `AdalySI1.RawUbarDerivNoLoop.loopVar_configMul_zero,
      `AdalySI1.L4Audit.rightTrivialized_mem_suTwo,
      `AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing paid declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in paid declaration {name}: {ax}"
  Lean.logInfo "C2_SPEC_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.C2Contract
