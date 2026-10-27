/-
C2 proof, build0. Owned directory: compute/m1_si1_c2_gated/build0/.
Target: the immutable `AdalySI1.C2Contract.C2Target` from ../spec/C2Target.lean.

Only paid declarations are applied; nothing is re-proved:
* C0: `AdalySI1.LeavesAuditC0.hasDerivAt_su2Log_loopVar_gInvOp` (log token -> gInvOp),
* C1: `AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent` (witness uniqueness),
  `AdalySI1.C1Proof.literal_deriv_frame` and `AdalySI1.C1Proof.near_dict` (four literal legs),
* A: `AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad`,
* B: `AdalySI1.Adjoint.gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad` (P_x Ad_W = N_x),
* zero-config rewrite `AdalySI1.RawUbarDerivNoLoop.loopVar_configMul_zero`,
* off-cut exp/log recovery `AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne`.

No fitting, positivity, nonzero-log, identity-loop exclusion, or flatness premise is
introduced. The only analytic premise is the pointwise `W_x ≠ -I` cut.
-/
import C2Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C2Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo RMap)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gInvOp)

variable {L : PeriodicLatticeExtent}

/-- THE ACCEPTED C2: literal log derivative equals the four log contributions.

Proof chain (no ingredient is re-proved):
1. Transport the off-cut premise to C0's varied-zero spelling via `loopVar_configMul_zero`.
2. Destruct paid C0; identify its existential tangent with C1's `rawLoopTangent` by
   `HasDerivAt.unique` against the paid C1 witness.
3. Identify the packaged `SuTwo` tangent with the four literal legs by `Subtype.ext`,
   using paid `literal_deriv_frame` and `near_dict`.
4. Prove `P_x Ad_{W_x} = N_x` by operator application: paid exp/log recovery gives
   `su2Exp ↑Zx = W`, paid A turns `RMap W v` into `expOp (adOp Zx) v`, and paid B
   collapses `gInvOp (-(adOp Zx)) (expOp (adOp Zx) v)` to `gInvOp (adOp Zx) v`.
5. Take C0's `.deriv`, substitute the packaged tangent, distribute the continuous
   linear maps, and apply step 4 to the two distinct negative leaves. -/
theorem su2Log_loopVar_deriv_eq_log4 : AdalySI1.C2Contract.C2Target := by
  intro L V0 A hah htr ell c x _hx hnc2
  show deriv (fun t : ℝ =>
      su2Log (loopVar 1 ell
        (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0
    = ((gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x))
        + gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2)))
        - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          (expOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x))))
        - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))
        : SuTwo) : M2)
  -- (1) C0's off-cut premise is spelled at the varied zero configuration.
  have hzero : loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x
      = loopVar 1 ell V0 c x :=
    AdalySI1.RawUbarDerivNoLoop.loopVar_configMul_zero V0 A ell c x
  have hnc2' : loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x
      ≠ su2NegOne := by
    rwa [hzero]
  -- (2) paid C0, then derivative-witness uniqueness against the paid C1 witness.
  obtain ⟨V, hW, hlog⟩ :=
    AdalySI1.LeavesAuditC0.hasDerivAt_su2Log_loopVar_gInvOp V0 A hah htr ell c x hnc2'
  have hderiv0 := hlog.deriv
  have hV : V = AdalySI1.C1Contract.rawLoopTangent V0 A ell c x :=
    hW.unique
      (AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent V0 A hah htr ell c x)
  have hderivLoop : deriv (fun t : ℝ => ((loopVar 1 ell
        (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)) 0
      = AdalySI1.C1Contract.rawLoopTangent V0 A ell c x :=
    (AdalySI1.C1Contract.hasDerivAt_actualLoop_rawLoopTangent V0 A hah htr ell c x).deriv
  -- (3) packaged tangent equals the four literal legs, by Subtype.ext.
  have hTS : ∀ (pf : V * Ring.inverse ((loopVar 1 ell
        (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x : SU2) : M2) ∈ suTwo),
      (⟨V * Ring.inverse ((loopVar 1 ell
          (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x : SU2) : M2), pf⟩ : SuTwo)
        = lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x)
          + RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2))
          - RMap (loopVar 1 ell V0 c x)
            (expOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (RMap (ubarSU2 1 ell V0 c)
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                  (coarseGammaPath 1 c.1 x))))
          - RMap (loopVar 1 ell V0 c x)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) := by
    intro pf
    apply Subtype.ext
    show V * Ring.inverse ((loopVar 1 ell
        (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x : SU2) : M2)
      = ((lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x)
          + RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2))
          - RMap (loopVar 1 ell V0 c x)
            (expOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (RMap (ubarSU2 1 ell V0 c)
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                  (coarseGammaPath 1 c.1 x))))
          - RMap (loopVar 1 ell V0 c x)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) : SuTwo) : M2)
    rw [hzero, hV, ← hderivLoop,
      AdalySI1.C1Proof.literal_deriv_frame V0 A hah htr ell c x,
      AdalySI1.C1Proof.near_dict V0 A hah htr c x]
    simp only [Submodule.coe_add, Submodule.coe_sub]
  -- (4) P_x Ad_{W_x} = N_x, from paid exp/log recovery, paid A, and paid B.
  have hexp : su2Exp ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2)
      = loopVar 1 ell V0 c x := by
    change su2Exp (su2Log (loopVar 1 ell V0 c x)) = loopVar 1 ell V0 c x
    exact AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne _ hnc2
  have hPW : ∀ v : SuTwo,
      gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (RMap (loopVar 1 ell V0 c x) v)
        = gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x))) v := by
    intro v
    have hrw : RMap (loopVar 1 ell V0 c x) v
        = expOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x))) v := by
      conv_lhs => rw [← hexp]
      exact AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad
        (principalSuTwoLog (loopVar 1 ell V0 c x)) v
    have happ : gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (expOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x))) v)
        = gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x))) v := by
      have h := congrArg (fun f : SuTwo →L[ℝ] SuTwo => f v)
        (AdalySI1.Adjoint.gInvOp_neg_ad_mul_expOp_ad_eq_gInvOp_ad
          (g := loopVar 1 ell V0 c x) hnc2)
      simpa using h
    rw [hrw, happ]
  -- (5) substitute and distribute; the two negative leaves stay separate.
  rw [hTS] at hderiv0
  rw [hzero] at hderiv0
  have hdist : gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
        (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x)
          + RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2))
          - RMap (loopVar 1 ell V0 c x)
            (expOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (RMap (ubarSU2 1 ell V0 c)
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                  (coarseGammaPath 1 c.1 x))))
          - RMap (loopVar 1 ell V0 c x)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)))
      = gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x))
        + gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
          (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x (List.replicate ell c.2)))
        - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          (expOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x))))
        - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)) := by
    simp only [map_add, map_sub, hPW]
  exact hderiv0.trans (congrArg (fun s : SuTwo => (s : M2)) hdist)

#print axioms su2Log_loopVar_deriv_eq_log4

end AdalySI1.C2Proof
