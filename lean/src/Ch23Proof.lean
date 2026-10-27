/-
CHANNELS 2 AND 3 PROOF — pays the exact
`AdalySI1.Ch23Contract.{Channel2Target, Channel3Target, BsigmaSplitTarget}`
frozen in `ch23/Ch23Target.lean` (NEXT.md §5.2, §5.3, and the §5 `Bsigma`
split). Owned directory: compute/m1_si1_asm2/ch23/. Authored in this owned
directory; proof shapes mirror the audited channel-1 proof at
compute/m1_si1_asm2/ch1/Ch1Proof.lean (same runner, same paid dependency
cluster, same standard-axiom fence).

Only paid declarations are applied; nothing from the paid cluster is
re-proved:

* L1 (`deps/L1ForwardCarrier.lean`, read-only):
  `unitSitesOf_one_image_eq_blockOf` — the `unitSitesOf 1 (1*ell) c.1`
  subtype carrier images EXACTLY onto `blockOf c.1 ell` (channel 3's
  reindexing).
* L2 (`deps/L2LineIntegralBridge.lean`, read-only):
  `unitToCoarseCov_one_eq_sum_blockOf` — the actual main term
  `unitToCoarseCov 1 ell V0 Aunit c'` IS its own `ell⁻⁴`-weighted plain
  `sigma` block sum (channel 2's entire geometric content);
  `fineDirToUnitBond` itself (`Aunit`).
* L6 (`deps/L6FittedSums.lean`, read-only, fitted under §4's hypotheses):
  `logData_Z_eq_ubarBracket` — the coefficient package's CARDINALITY MEAN
  `LogData.Z (sourcePrincipalLogData 1 ell V0) c'` IS the raw
  `w = ell⁻³`-weighted `ubarBracket` package `Z`; used ONLY for the operator
  `G` in the `Bsigma` split's per-site identity, never as a substitute for a
  summand weight.
* base package: `AdalyFormal.Balaban.QjComposite.stepBlockOf_one`
  (`stepBlockOf c.1 1 ell = blockOf c.1 ell`).

Proof routes (raw `ell⁻³` weight throughout; no fitted cardinality mean is
substituted for a summand weight; no `Dcomputed` claim; no single-channel
claim; no commutation of operators from different backgrounds/logarithms):

1. `hsc` (channels 2 and 3): real scalar algebra
   `(ell:ℝ) * (1/(ell:ℝ)^4) = ((ell:ℝ)^3)⁻¹` from `0 < ell` — the
   `ell⁻⁴`-normalized q channels rescaled by `(ell:ℝ)` carry exactly the raw
   `ell⁻³` weight.
2. Channel 2: paid L2 expands `unitToCoarseCov 1 ell V0 Aunit c'` into its
   plain `sigma` block sum over `blockOf c'.1.1 ell` (definitionally
   `blockOf c.1 ell`); `smul_smul`/`hsc`/`Finset.smul_sum` rescale to the
   raw weight, and base-package `stepBlockOf_one` identifies the carriers.
   One coercion lift by `Submodule.coe_smul` closes the `M2` statement.
3. Channel 3: `term3` unfolds at the corrected coefficient, rescales by
   `hsc`, and reindexes from the `unitSitesOf` subtype carrier onto
   `blockOf c.1 ell` (paid L1), then `stepBlockOf_one`; one coercion lift
   closes. No fitted bridge is needed at this channel: both sides already
   carry the corrected `coeff.E1`.
4. `Bsigma` split: `hZ` (paid L6, used only for `G`'s logarithm package) and
   the definitional site logs `hZx` give `hE1 : coeff.E1 c' x = G * P x - 1`
   with RAW operators — the NEXT.md §5 spelling after the fitted raw-Z
   bridge, not a commutation. Pointwise, `G (P x s) = coeff.E1 c' x s + s`
   by the CLM split; `smul_add`, `Finset.sum_add_distrib`, and one
   `Submodule.coe_add` lift give `Bsigma =` plain mean `+` `E1`-mean.

No `W_x ≠ -I` premise is needed: no exp/log recovery is invoked at these
channels. No `sorry`, no placeholder, no assumed target.
-/
import Ch23Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch23Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov
  (coarseGammaPath coarsePathHolonomy unitToCoarseCov)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp gOp gInvOp term3)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-2 PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch23Contract.Channel2Target` (NEXT.md §5.2): the raw
`ell⁻³`-weighted plain `sigma` mean over the literal
`S = stepBlockOf c.1 1 ell`, coerced to `M2`, IS the `(ell : ℝ)`-rescaled
coercion of the actual main term `unitToCoarseCov 1 ell V0 Aunit c'`.
Quantifiers and premises exactly as frozen; arbitrary extent, arbitrary
(generally nonflat) background, arbitrary anti-Hermitian traceless field. -/
theorem channel2_sigma_mean : AdalySI1.Ch23Contract.Channel2Target := by
  intro L V0 A hah htr ell c hcell hell hdvd
  -- the target's own literal coarse cast, abstracted once for reuse
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) scalar algebra: `(ell:ℝ) • ell⁻⁴ = ell⁻³`, needing only `0 < ell`.
  have h0 : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hsc : (ell : ℝ) * (1 / (ell : ℝ) ^ 4) = ((ell : ℝ) ^ 3)⁻¹ := by
    field_simp
  -- (2) paid L2: the actual main term IS the `ell⁻⁴` plain `sigma` block sum.
  have hL2 : unitToCoarseCov 1 ell V0 (fineDirToUnitBond A hah htr) c'
      = (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c.1 ell,
          RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
              (List.replicate ell c.2)) :=
    unitToCoarseCov_one_eq_sum_blockOf ell V0 (fineDirToUnitBond A hah htr) c'
  -- (3) the raw-weight `SuTwo` equality: rescale by `hsc`, distribute the
  -- weight into the sum, and identify the carriers by `stepBlockOf_one`.
  have hmain : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
            (List.replicate ell c.2)) : SuTwo)
      = (ell : ℝ) • unitToCoarseCov 1 ell V0 (fineDirToUnitBond A hah htr) c' := by
    rw [hL2, smul_smul, hsc, Finset.smul_sum,
      AdalyFormal.Balaban.QjComposite.stepBlockOf_one]
  -- (4) one coercion lift closes the `M2` statement.
  rw [hmain, Submodule.coe_smul]

/-- **THE CHANNEL-3 PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch23Contract.Channel3Target` (NEXT.md §5.3): the raw
`ell⁻³`-weighted `E1`-mean of `sigma` over the literal `S`, coerced to `M2`,
IS the `(ell : ℝ)`-rescaled coercion of
`OneStep124.term3 1 ell V0 coeff Aunit c'` at the CORRECTED principal
coefficient record. Same quantifiers and premises. -/
theorem channel3_E1_sigma_mean : AdalySI1.Ch23Contract.Channel3Target := by
  intro L V0 A hah htr ell c hcell hell hdvd
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) the same scalar algebra.
  have h0 : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hsc : (ell : ℝ) * (1 / (ell : ℝ) ^ 4) = ((ell : ℝ) ^ 3)⁻¹ := by
    field_simp
  -- (2) `(ell:ℝ) • term3` unfolds at the corrected coefficient and rescales
  -- by `hsc`, distributing the raw weight into the subtype-carrier sum.
  have hR : (ell : ℝ) •
        (term3 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo)
      = ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
          ((ell : ℝ) ^ 3)⁻¹ •
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' u.1
              (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 u.1))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) u.1
                  (List.replicate ell c.2))) := by
    show (ell : ℝ) • ((1 / (ell : ℝ) ^ 4) •
        ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' u.1
            (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 u.1))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) u.1
                (List.replicate ell c.2))))
      = _
    rw [smul_smul, hsc, Finset.smul_sum]
  -- (3) reindex the `unitSitesOf` subtype carrier onto the raw block (paid
  -- L1), and identify `stepBlockOf c.1 1 ell` with it (base package).
  have hmain : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
          (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
              (List.replicate ell c.2))) : SuTwo)
      = (ell : ℝ) • (term3 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo) := by
    rw [hR, AdalyFormal.Balaban.QjComposite.stepBlockOf_one,
      ← unitSitesOf_one_image_eq_blockOf c.1 ell,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  -- (4) one coercion lift closes the `M2` statement.
  rw [hmain, Submodule.coe_smul]

/-- **THE EXPLICIT `Bsigma` SPLIT PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch23Contract.BsigmaSplitTarget`: C3's literal second raw leaf
`Bsigma = ↑(Σ x∈S, w • G (P x (sigma x)))` IS the plain `sigma` mean PLUS the
`E1`-mean of `sigma`, both raw-weighted and coerced. The only fitted input is
paid L6's `logData_Z_eq_ubarBracket`, used solely to rewrite the logarithm
package INSIDE the operator `G`; the per-site identity
`G (P x s) = s + coeff.E1 c' x s` is the NEXT.md §5 spelling
`E1_x = G * P_x - 1` at the SAME site with the SAME raw `Z` — no commutation
of operators from different backgrounds or logarithms. -/
theorem bsigma_split_plain_add_E1 : AdalySI1.Ch23Contract.BsigmaSplitTarget := by
  intro L V0 A hah htr ell c hcell hell hdvd
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) the fitted raw-Z bridge (paid L6) and the definitional site logs.
  have hZ : OneStep124.LogData.Z (sourcePrincipalLogData 1 ell V0) c'
      = (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo) :=
    logData_Z_eq_ubarBracket hdvd V0 c'
  have hZx : ∀ x : PeriodicLatticeSite L,
      (sourcePrincipalLogData 1 ell V0).Zx c' x
        = principalSuTwoLog (loopVar 1 ell V0 c x) :=
    fun x => rfl
  -- (2) `E1_x = G * P_x - 1` at the corrected coefficient, raw operators.
  have hE1 : ∀ x : PeriodicLatticeSite L,
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
        = gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
          * gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))) - 1 := by
    intro x
    show gOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Z c')))
        * gInvOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Zx c' x))) - 1 = _
    rw [hZ, hZx x]
  -- (3) pointwise CLM split: `G (P_x s) = coeff.E1 c' x s + s`.
  have happ : ∀ x : PeriodicLatticeSite L, ∀ s : SuTwo,
      gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo)))
        (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))) s)
      = (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x s
        + s := by
    intro x s
    rw [hE1 x, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, sub_add_cancel]
  -- (4) per-site raw-weight identity, plain mean first.
  have hsite : ∀ x : PeriodicLatticeSite L,
      ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
              (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                  (List.replicate ell c.2))))
        = ((ell : ℝ) ^ 3)⁻¹ •
            RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                (List.replicate ell c.2))
          + ((ell : ℝ) ^ 3)⁻¹ •
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
              (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                  (List.replicate ell c.2))) := by
    intro x
    rw [happ x _, smul_add]
    exact add_comm _ _
  -- (5) sum over the literal `S` and lift through the `M2` coercion.
  have hsum : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
            (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                (List.replicate ell c.2)))) : SuTwo)
      = (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                (List.replicate ell c.2)) : SuTwo)
        + (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
              (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                  (List.replicate ell c.2))) : SuTwo) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hsite x)
  rw [hsum]
  exact Submodule.coe_add _ _

#print axioms channel2_sigma_mean
#print axioms channel3_E1_sigma_mean
#print axioms bsigma_split_plain_add_E1

-- Fresh existence/axiom receipts for the exact paid declarations this proof applies.
#print axioms unitToCoarseCov_one_eq_sum_blockOf
#print axioms unitSitesOf_one_image_eq_blockOf
#print axioms logData_Z_eq_ubarBracket
#print axioms AdalyFormal.Balaban.QjComposite.stepBlockOf_one

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Ch23Proof.channel2_sigma_mean,
      `AdalySI1.Ch23Proof.channel3_E1_sigma_mean,
      `AdalySI1.Ch23Proof.bsigma_split_plain_add_E1,
      `unitToCoarseCov_one_eq_sum_blockOf,
      `unitSitesOf_one_image_eq_blockOf,
      `logData_Z_eq_ubarBracket,
      `AdalyFormal.Balaban.QjComposite.stepBlockOf_one] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing channels-2/3 declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in channels-2/3 declaration {name}: {ax}"
  for mod in [`Ch23Target, `L2LineIntegralBridge, `L6FittedSums, `L1ForwardCarrier,
      `T1MainSegment, `RawUbarDerivNoLoop, `IngredientDeriv, `RawAverageDeriv,
      `AdalyFormal.Balaban.QjComposite, `AdalyFormal.Balaban.ThirdLevelArrows,
      `AdalyFormal.Balaban.AdmissibleSubspace, `AdalyFormal.Balaban.TowerLawCovariant,
      `AdalyFormal.Balaban.UbarTowerCovariance,
      `AdalyFormal.Balaban.CovariantOperators] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"CH23_RESOLVED {mod}: {path}"
  Lean.logInfo "CH23_PROOF_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.Ch23Proof
