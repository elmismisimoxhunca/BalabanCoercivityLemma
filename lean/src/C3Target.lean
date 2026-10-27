/-
C3 CONTRACT ONLY: executable proposition, NOT a proof of C3.
Owned directory: compute/m1_si1_c3_gated/spec/.
All imported campaign modules resolve to the packaged read-only ../deps cluster.

This definition freezes ONLY the second additive matrix slot occurring in
`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`.
It does not include the endpoint terms `Aminus` or `Cplus`, does not identify the
full derivative `Dcomputed`, and does not isolate one coefficient channel.

The right side retains all five raw leaves: four weighted leaves and the positive
outside direct term `Bout`.  A proposition definition that elaborates is not a
proof of the equality.
-/
import ProdFullAssembleDerivNoLoop
import C2Proof
import DexpSumAudit
import Adjoint
import L2LineIntegralBridge
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C3Contract

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar cPlusS coarseBondVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.RawAverageDeriv (holonomyDirDeriv)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp)

variable {L : PeriodicLatticeExtent}

/-- UNPROVED raw C3 equality for the literal product-rule slot.

All objects are frozen at the arbitrary background `V0`, at stride `1`:
* `S = stepBlockOf c.1 1 ell`;
* `q x = coarseGammaPath 1 c.1 x` and `r = List.replicate ell c.2`;
* `p x = coarsePathHolonomy 1 V0 c.1 (q x)`;
* `C = coarseBondVar 1 ell V0 c`, `K = ubarSU2 1 ell V0 c`;
* `W x = loopVar 1 ell V0 c x`, `Zx x = principalSuTwoLog (W x)`;
* `Z` packages the literal raw weighted `ubarBracket`, not a principal log of
  `K` and not a fitted/cardinality mean;
* `tauSu`, `sigmaSu`, `phiSu`, and `dSu` are the literal near,
  shifted-segment, untranslated raw far-list, and direct line-integral leaves.

`Bfar` and `Bdirect` retain their negative signs. `Bout` is positive, has no
weight, and remains outside every finite sum. No partner-list L5 substitution,
coefficient match, endpoint cancellation, or commutation of distinct frozen
background operators is part of this proposition. -/
def C3Point (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) : Prop :=
  let Aunit : CoarseBond L 1 → SuTwo := fineDirToUnitBond A hah htr
  let S : Finset (PeriodicLatticeSite L) := stepBlockOf c.1 1 ell
  let q : PeriodicLatticeSite L → List (Fin 3) := fun x => coarseGammaPath 1 c.1 x
  let r : List (Fin 3) := List.replicate ell c.2
  let p : PeriodicLatticeSite L → SU2 := fun x => coarsePathHolonomy 1 V0 c.1 (q x)
  let C : SU2 := coarseBondVar 1 ell V0 c
  let K : SU2 := ubarSU2 1 ell V0 c
  let W : PeriodicLatticeSite L → SU2 := fun x => loopVar 1 ell V0 c x
  let Zx : PeriodicLatticeSite L → SuTwo := fun x => principalSuTwoLog (W x)
  let Z : SuTwo := ⟨ubarBracket V0 ell c,
    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
  let w : ℝ := ((ell : ℝ) ^ 3)⁻¹
  let tauSu : PeriodicLatticeSite L → SuTwo := fun x =>
    lineIntegral 1 V0 Aunit c.1 (q x)
  let sigmaSu : PeriodicLatticeSite L → SuTwo := fun x =>
    RMap (p x) (lineIntegral 1 V0 Aunit x r)
  let phiSu : PeriodicLatticeSite L → SuTwo := fun x =>
    lineIntegral 1 V0 Aunit (cPlusS 1 ell c) (q x)
  let dSu : SuTwo := lineIntegral 1 V0 Aunit c.1 r
  let P : PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo) := fun x =>
    gInvOp (-(adOp (Zx x)))
  let N : PeriodicLatticeSite L → (SuTwo →L[ℝ] SuTwo) := fun x =>
    gInvOp (adOp (Zx x))
  let G : SuTwo →L[ℝ] SuTwo := gOp (-(adOp Z))
  let Jminus : SuTwo →L[ℝ] SuTwo := expOp (-(adOp Z))
  let Jplus : SuTwo →L[ℝ] SuTwo := expOp (adOp Z)
  let Btau : M2 := ((∑ x ∈ S, w • G (P x (tauSu x)) : SuTwo) : M2)
  let Bsigma : M2 := ((∑ x ∈ S, w • G (P x (sigmaSu x)) : SuTwo) : M2)
  let Bfar : M2 := -((∑ x ∈ S,
    w • G (N x (Jminus (RMap K (phiSu x)))) : SuTwo) : M2)
  let Bdirect : M2 := -((∑ x ∈ S, w • G (N x dSu) : SuTwo) : M2)
  let Bout : M2 := ((Jplus dSu : SuTwo) : M2)
  ((fderiv ℝ (NormedSpace.exp : M2 → M2) (ubarBracket V0 ell c))
      (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        deriv (fun t : ℝ =>
          su2Log (loopVar 1 ell
            (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
      * ((C : SU2) : M2)
    + ((su2Exp (ubarBracket V0 ell c) : SU2) : M2)
        * holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))
    * ((K : SU2) : M2)ᴴ
    = Btau + Bsigma + Bfar + Bdirect + Bout

/-- THE SINGLE C3 ACCEPTANCE TARGET (UNPROVED).

Quantification is over an arbitrary lattice extent, arbitrary generally nonflat
background, and arbitrary anti-Hermitian traceless matrix field. The sole
additional analytic premise is the blockwise principal-log cut on the literal
`S`; all identity-loop sites remain admitted. There is no positivity, fitting,
divisibility, nonzero-log, flatness, support, gauge-direction, L5, or endpoint
premise. -/
def C3Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L),
    (∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) →
    C3Point V0 A hah htr ell c

/-
Future proof-owner interface (SIGNATURE ONLY; no theorem with this name exists here):

  theorem AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves :
    AdalySI1.C3Contract.C3Target

Elaboration of this proposition is not a proof. The future theorem must inhabit
this exact target and pass the separate immutable acceptance template.
-/

#print C3Point
#print C3Target
#print axioms C3Point
#print axioms C3Target

-- Fresh existence/axiom receipts for the exact source and paid declarations pinned by C3.
#print axioms AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop
#print axioms AdalySI1.C2Proof.su2Log_loopVar_deriv_eq_log4
#print axioms AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar
#print axioms AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul
#print axioms AdalySI1.DexpSumAudit.dexp_sum_apply
#print axioms AdalySI1.DexpRodrigues.dexp_eq_gOp
#print axioms holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral
#print axioms AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop,
      `AdalySI1.C2Proof.su2Log_loopVar_deriv_eq_log4,
      `AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar,
      `AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul,
      `AdalySI1.DexpSumAudit.dexp_sum_apply,
      `AdalySI1.DexpRodrigues.dexp_eq_gOp,
      `holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral,
      `AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing C3 source/paid declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in C3 source/paid declaration {name}: {ax}"
  for mod in [`ProdFullAssembleDerivNoLoop, `C2Proof, `C2Target, `DexpSumAudit,
      `DexpRodriguesG, `Adjoint, `L2LineIntegralBridge, `RawUbarDerivNoLoop] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"C3_RESOLVED {mod}: {path}"
  Lean.logInfo "C3_SPEC_SOURCE_AND_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.C3Contract
