/-
C1 CONTRACT ONLY: executable proposition, NOT a proof of C1.
Owned directory: compute/m1_si1_c1_gated/contract/.
Read-only paid roots: ../deps/Adjoint and ../deps/L2LineIntegralBridge.
See CONTRACT.md for the source equations, acceptance gate, and pending L5 bridge.

The only theorem below repackages the ALREADY PAID literal loop derivative by
exact definitional equality. It proves neither the four-leg split nor the frame
change. No logarithmic derivative (C0), adjoint identity (A/B), or SI1 is repaid.
-/
import Adjoint
import L2LineIntegralBridge

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C1Contract

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.Q1Real (GammaPath)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.IngredientDeriv (dirDeriv)
open AdalySI1.RawAverageDeriv (holonomyDirDeriv)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp)

variable {L : PeriodicLatticeExtent}

/-- EXACT ambient coefficient in RawUbarDerivNoLoop.hasDerivAt_loopVar_configMul.
The far leg is the inverse of the forward holonomy on the SAME near-tree list,
based at cPlusS. The closing derivative is the full replicate-ell direct path.
No free tangent variables, choice of existential witness, or target equality. -/
def rawLoopTangent (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (ell : ℕ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : M2 :=
  let p : SU2 := coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x)
  let s : SU2 := coarsePathHolonomy 1 V0 x (List.replicate ell c.2)
  let f : SU2 := coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x)
  let C : SU2 := coarseBondVar 1 ell V0 c
  let pdot : M2 := holonomyDirDeriv V0 A 1 c.1 (coarseGammaPath 1 c.1 x)
  let sdot : M2 := holonomyDirDeriv V0 A 1 x (List.replicate ell c.2)
  let fdot : M2 := holonomyDirDeriv V0 A 1 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x)
  let Cdot : M2 := holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2)
  (((pdot * (s : M2) + (p : M2) * sdot) * (f : M2)ᴴ
      + ((p : M2) * (s : M2)) * fdotᴴ) * (C : M2)ᴴ)
    + ((gammaVarStrided 1 ell V0 c x : SU2) : M2) * Cdotᴴ

/-- PAID-type transcription check, not C1. `exact` checks the coefficient against
the actual imported declaration; this also supplies the derivative witness for
C1's literal `deriv` token without differentiating the loop again. -/
theorem hasDerivAt_actualLoop_rawLoopTangent
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    HasDerivAt
      (fun t : ℝ => ((loopVar 1 ell
        (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2))
      (rawLoopTangent V0 A ell c x) 0 :=
  AdalySI1.RawUbarDerivNoLoop.hasDerivAt_loopVar_configMul V0 A hah htr ell c x

/-- UNPROVED C1 at a point. Four obligations, in this fixed conjunction order:
(1) near-tree campaign dictionary; (2) four raw right-trivialized legs;
(3) direct-to-blocked frame for every SuTwo input; (4) the ACTUAL loop derivative
in that blocked frame, retaining both negative inverse legs separately.

All ingredients are fixed at V0. Z is the raw mean bracket packaged into SuTwo,
NOT principalSuTwoLog K and NOT the cardinality-normalized q mean off fitted
geometry. phi uses the literal far leg's list, not an unproved partner rewrite.
-/
def C1Point (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : Prop :=
  let q : List (Fin 3) := coarseGammaPath 1 c.1 x
  let r : List (Fin 3) := List.replicate ell c.2
  let p : SU2 := coarsePathHolonomy 1 V0 c.1 q
  let s : SU2 := coarsePathHolonomy 1 V0 x r
  let f : SU2 := coarsePathHolonomy 1 V0 (cPlusS 1 ell c) q
  let C : SU2 := coarseBondVar 1 ell V0 c
  let W : SU2 := loopVar 1 ell V0 c x
  let K : SU2 := ubarSU2 1 ell V0 c
  let Z : SuTwo := ⟨ubarBracket V0 ell c,
    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
  let Aunit := fineDirToUnitBond A hah htr
  let tau : M2 := dirDeriv V0 A c.1 (GammaPath c.1 x) 1
  let sigma : SuTwo := RMap p (lineIntegral 1 V0 Aunit x r)
  let phi : SuTwo := lineIntegral 1 V0 Aunit (cPlusS 1 ell c) q
  let d : SuTwo := lineIntegral 1 V0 Aunit c.1 r
  let rho : M2 := rawLoopTangent V0 A ell c x * Ring.inverse (W : M2)
  -- (1) tau is the right-trivialized near tree, not an ambient holonomy derivative.
  (tau = (lineIntegral 1 V0 Aunit c.1 q : M2)) ∧
  -- (2) +near, +shifted segment, -inverse far tree, -inverse direct closure.
  (rho = tau + (sigma : M2)
    - (RMap (p * s * f⁻¹) phi : M2) - (RMap W d : M2)) ∧
  -- (3) C = exp(-Z) K in adjoint form: the minus operator MUST precede RMap K.
  (∀ v : SuTwo, RMap C v = expOp (-(adOp Z)) (RMap K v)) ∧
  -- (4) final literal derivative target, not a detached generic product identity.
  (deriv (fun t : ℝ => ((loopVar 1 ell
      (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)) 0
      * Ring.inverse (W : M2)
    = tau + (sigma : M2)
      - (RMap W (expOp (-(adOp Z)) (RMap K phi)) : M2)
      - (RMap W d : M2))

/-- THE SINGLE ACCEPTANCE TARGET (UNPROVED).
C1 is pointwise on the actual near-block carrier, stride 1 and block factor ell.
No flatness, gradient-only restriction, identity-loop exclusion, log-chart cut,
fitting assumption, or assumed target/bridge equality is present. C1 involves
only a matrix derivative; the off-minus-identity cut is needed later by C0/C2.
-/
def C1Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L),
    x ∈ stepBlockOf c.1 1 ell → C1Point V0 A hah htr ell c x

/-- SEPARATE UNPROVED L5 specification, NOT a hypothesis of C1Target.
Needed to replace phi's raw staircase by term4's named partner staircase.
This contract does not claim a certificate for that path equality. Fitting is
retained explicitly for the source/q application (not claimed minimal for L5).
-/
def L5FarPathBridgeTarget : Prop :=
  ∀ {L : PeriodicLatticeExtent} (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell),
    0 < ell → (∀ μ : Fin 3, ell ∣ (L μ + 1)) →
    ∀ x : PeriodicLatticeSite L, x ∈ stepBlockOf c.1 1 ell →
      let c' : AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1 * ell) :=
        (⟨c.1, by rw [one_mul]; exact hcell⟩, c.2)
      coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' x)
        = coarseGammaPath 1 c.1 x

/-
Future proof-owner interface (SIGNATURE ONLY; no theorem with this name exists here):

  theorem AdalySI1.C1Proof.loopVar_rightTrivialized_eq_four_legs :
    AdalySI1.C1Contract.C1Target

The future proof module must import C1Target, provide an actual proof of that
signature, and print its axioms freshly. A proof of C1Target's TYPE being Prop,
this file's HasDerivAt wrapper, only conjunct (2), or L5FarPathBridgeTarget alone
is not an acceptable C1 proof. See CONTRACT.md for the exact downstream check.
-/

#print C1Target
#print C1Point
#print L5FarPathBridgeTarget
#print axioms rawLoopTangent
#print axioms hasDerivAt_actualLoop_rawLoopTangent
#print axioms C1Point
#print axioms C1Target
#print axioms L5FarPathBridgeTarget
-- Fresh paid-declaration checks; imports are not recompilations or new payment.
#print axioms AdalySI1.RawUbarDerivNoLoop.hasDerivAt_loopVar_configMul
#print axioms GammaPath_eq_coarseGammaPath_one_map
#print axioms holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral
#print axioms dirDeriv_map_true_one_eq_lineIntegral
#print axioms AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar
#print axioms AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad

end AdalySI1.C1Contract
