/-
C3 proof, build0. Owned directory: compute/m1_si1_c3_gated/build0/.
Target: the immutable `AdalySI1.C3Contract.C3Target` from ../spec/C3Target.lean
(SHA-256 41c67fa83bc14b74d7a588937f1ae5b0c0724ac5ae358c47c8c5b1621a40d008).

Only paid declarations are applied; nothing is re-proved:
* C2: `AdalySI1.C2Proof.su2Log_loopVar_deriv_eq_log4` (literal four-leaf log derivative),
* raw K identity: `AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar`,
* dexp distribution: `AdalySI1.DexpSumAudit.dexp_sum_apply` (whose underlying
  `AdalySI1.DexpRodrigues.dexp_eq_gOp` is unconditional, including `Z = 0`),
* L2: `AdalySI1.C1Proof.holonomy_tangent` (replicate direct segment),
* SU2 exp inverse: `AdalySI1.C1Proof.su2Exp_neg_mul`,
* paid A: `AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad`.

The matrix cancellation `(C : M2) (K : M2)ᴴ = exp (-(Z : M2))` is proved here from the
raw K identity, SU2 adjoint/inverse laws, and the paid exp coercion; `C` is never
commuted with `exp Z`. `Bout` is positive, unweighted, and outside the finite sum.
No L5 partner-list bridge, cardinality-mean conversion, endpoint cancellation,
channel coefficient match, fitting, positivity, nonzero-log, flatness, support, or
gauge-direction premise is introduced. The only analytic premise is the blockwise
`W_x ≠ -I` cut on the literal `S`; all identity-loop sites remain admitted.
-/
import C3Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.C3Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne coe_mul coe_inv coe_one
  mul_star_self su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_coe_apply)
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

/-- THE ACCEPTED C3: the literal second additive slot of
`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`
equals the five raw leaves `Btau + Bsigma + Bfar + Bdirect + Bout`.

Proof chain (no ingredient is re-proved):
1. Substitute the certified C2 four-leaf log derivative pointwise, using
   `Finset.sum_congr` so the off-cut premise `hnc2` is applied only at `x ∈ S`.
2. Prove the matrix identity `(C : M2) * (K : M2)ᴴ = NormedSpace.exp (-(Z : M2))`
   from the raw identity `K = su2Exp ↑Z * C`: reverse the product under `ᴴ`,
   cancel the adjacent `C * Cᴴ` (never commuting `C` past `exp Z`), and identify
   the exponential adjoint `(su2Exp ↑Z : M2)ᴴ` with `NormedSpace.exp (-(Z : M2))`
   via the paid `su2Exp_neg_mul` inverse law and the paid exp coercion.
3. Apply the paid `dexp_sum_apply` at the raw bracket `Z` with the complete
   four-leaf `D x`; distribute `G`, the real weight, and the two sums over the two
   additions and two subtractions, preserving `G ∘ N_x ∘ Jminus ∘ RMap K` in the
   far leaf.
4. Reuse paid L2 on `List.replicate ell c.2` to get `Cdot = ↑dSu * ↑C`; combine
   with the matrix cancellation and paid A to identify the outside term
   `e^Z d e^{-Z} = Ad_{e^Z} d = Jplus d`, the positive unweighted `Bout`. -/
theorem prod_slotB_eq_five_raw_leaves : AdalySI1.C3Contract.C3Target := by
  intro L V0 A hah htr ell c hnc2
  unfold AdalySI1.C3Contract.C3Point
  dsimp only
  -- (1) pointwise certified C2 substitution on the literal block `S`.
  have hc2 : ∀ x ∈ stepBlockOf c.1 1 ell,
      deriv (fun t : ℝ =>
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
            : SuTwo) : M2) :=
    fun x hx => AdalySI1.C2Proof.su2Log_loopVar_deriv_eq_log4 V0 A hah htr ell c x hx
      (hnc2 x hx)
  have hsum : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        deriv (fun t : ℝ =>
          su2Log (loopVar 1 ell
            (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
      = ∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        ((gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
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
            : SuTwo) : M2) :=
    Finset.sum_congr rfl (fun x hx => congrArg (((ell : ℝ) ^ 3)⁻¹ • ·) (hc2 x hx))
  -- (2) the exponential adjoint and the matrix cancellation `C Kᴴ = exp (-Z)`.
  have hExpAdj : (((su2Exp ((⟨ubarBracket V0 ell c,
          ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2))
        : SU2) : M2)ᴴ = NormedSpace.exp (-(ubarBracket V0 ell c)) := by
    have h1 : su2Exp ((-⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2)
        = (su2Exp ((⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2))⁻¹ :=
      eq_inv_of_mul_eq_one_left (AdalySI1.C1Proof.su2Exp_neg_mul ⟨ubarBracket V0 ell c,
        ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩)
    rw [← coe_inv, ← h1]
    exact su2Exp_coe_of_antiHerm_traceless
      (-⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.1
      (-⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.2
  have hCK : ((coarseBondVar 1 ell V0 c : SU2) : M2)
        * (((ubarSU2 1 ell V0 c : SU2) : M2))ᴴ
      = NormedSpace.exp (-(ubarBracket V0 ell c)) := by
    rw [AdalySI1.RawUbarDerivNoLoop.ubarSU2_eq_exp_bracket_mul_bondVar,
      coe_mul, Matrix.conjTranspose_mul, ← mul_assoc, mul_star_self, one_mul]
    exact hExpAdj
  -- (3) paid dexp distribution at the raw bracket `Z`, with the complete four-leaf `D x`.
  have hdexp : (fderiv ℝ (NormedSpace.exp : M2 → M2) (ubarBracket V0 ell c))
        (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          ((gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (coarseGammaPath 1 c.1 x))
              + gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                    (List.replicate ell c.2)))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (expOp (-(adOp ⟨ubarBracket V0 ell c,
                    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
                  (RMap (ubarSU2 1 ell V0 c)
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                      (coarseGammaPath 1 c.1 x))))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))
              : SuTwo) : M2))
        * NormedSpace.exp (-(ubarBracket V0 ell c))
      = ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (coarseGammaPath 1 c.1 x))
              + gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                    (List.replicate ell c.2)))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (expOp (-(adOp ⟨ubarBracket V0 ell c,
                    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
                  (RMap (ubarSU2 1 ell V0 c)
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                      (coarseGammaPath 1 c.1 x))))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
          : SuTwo) : M2) :=
    AdalySI1.DexpSumAudit.dexp_sum_apply (stepBlockOf c.1 1 ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      ⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
      (fun x =>
        gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
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
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
  -- the weighted `G`-sum distributes over the four leaves.
  have hdist : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        gOp (-(adOp ⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
          (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
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
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
        : SuTwo)
      = (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x)))
          : SuTwo)
        + (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                    (List.replicate ell c.2))))
            : SuTwo)
        - (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (expOp (-(adOp ⟨ubarBracket V0 ell c,
                    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
                  (RMap (ubarSU2 1 ell V0 c)
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                      (coarseGammaPath 1 c.1 x)))))
            : SuTwo)
        - (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
            : SuTwo) := by
    have step : ∀ x ∈ stepBlockOf c.1 1 ell,
        ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
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
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
        = ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (coarseGammaPath 1 c.1 x)))
          + ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                    (List.replicate ell c.2))))
          - ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (expOp (-(adOp ⟨ubarBracket V0 ell c,
                    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
                  (RMap (ubarSU2 1 ell V0 c)
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                      (coarseGammaPath 1 c.1 x)))))
          - ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp ⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
              (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))) :=
      fun x _ => by simp only [map_add, map_sub, smul_add, smul_sub]
    rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  -- (4) the outside term: `e^Z Cdot Kᴴ = Ad_{e^Z} d = Jplus d`, positive and unweighted.
  have hE1 : ((su2Exp (ubarBracket V0 ell c) : SU2) : M2)
      = NormedSpace.exp ((⟨ubarBracket V0 ell c,
          ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2) :=
    su2Exp_coe_of_antiHerm_traceless
      (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.1
      (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.2
  have hE2 : ((su2Exp ((⟨ubarBracket V0 ell c,
          ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2) : SU2)
        : M2)
      = NormedSpace.exp ((⟨ubarBracket V0 ell c,
          ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2) :=
    su2Exp_coe_of_antiHerm_traceless
      (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.1
      (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
        ubarBracket_trace V0 ell c⟩ : SuTwo).2.2
  have hassoc : ∀ (a b c d : M2), (a * (b * c)) * d = a * b * (c * d) :=
    fun a b c d => by rw [← mul_assoc a b, mul_assoc (a * b) c d]
  have hOut : (((su2Exp (ubarBracket V0 ell c) : SU2) : M2)
        * holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))
        * (((ubarSU2 1 ell V0 c : SU2) : M2))ᴴ
      = ((expOp (adOp ⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩)
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))
        : SuTwo) : M2) := by
    have hL2 : holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2)
        = ((lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)
            : SuTwo) : M2) * ((coarseBondVar 1 ell V0 c : SU2) : M2) :=
      AdalySI1.C1Proof.holonomy_tangent V0 A hah htr c.1 (List.replicate ell c.2)
    have hPaidA : RMap (su2Exp ((⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩ : SuTwo) : M2))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))
        = expOp (adOp ⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩)
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)) :=
      AdalySI1.Adjoint.rmap_su2Exp_apply_eq_expOp_ad ⟨ubarBracket V0 ell c,
        ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩
        (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2))
    rw [hL2, hassoc, hCK, hE1, ← hPaidA, RMap_coe_apply, hExpAdj, hE2]
  -- (5) assemble the two additive pieces against the five raw leaves.
  have hT1 : ((fderiv ℝ (NormedSpace.exp : M2 → M2) (ubarBracket V0 ell c))
        (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          deriv (fun t : ℝ =>
            su2Log (loopVar 1 ell
              (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
        * ((coarseBondVar 1 ell V0 c : SU2) : M2))
        * (((ubarSU2 1 ell V0 c : SU2) : M2))ᴴ
      = ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp ⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (coarseGammaPath 1 c.1 x))
              + gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                    (List.replicate ell c.2)))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (expOp (-(adOp ⟨ubarBracket V0 ell c,
                    ubarBracket_conjTranspose V0 ell c, ubarBracket_trace V0 ell c⟩))
                  (RMap (ubarSU2 1 ell V0 c)
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                      (coarseGammaPath 1 c.1 x))))
              - gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1 (List.replicate ell c.2)))
          : SuTwo) : M2) := by
    rw [mul_assoc, hCK, hsum, hdexp]
  rw [add_mul, hT1, hOut, hdist]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

#print axioms prod_slotB_eq_five_raw_leaves

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing C3 theorem: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {name}: {ax}"
  Lean.logInfo "C3_PROOF_STANDARD_AXIOMS_PASS"

end AdalySI1.C3Proof
