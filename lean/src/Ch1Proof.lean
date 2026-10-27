/-
CHANNEL 1 PROOF — pays the exact `AdalySI1.Ch1Contract.Channel1Target`
frozen in `ch1/Ch1Target.lean` (NEXT.md §5.1). Owned directory:
compute/m1_si1_asm2/ch1/. No arbitrary stage deadline was applied; the
proof was completed and compiled before any checkpoint.

Handoff note (m1_si1_asm2/ch1): copied byte-identical from
compute/m1_si1_assembly/ch1/Ch1Proof.lean (SHA-256
6a3419fad902eb4bb3dd3588c3095b01e12d69de5cdef279f76b99b82c596a85) and fixed
its one real error: in `hsc` the `field_simp` call already closes the goal,
so the following `ring` failed with "No goals to be solved" (assembly dev2,
line 102) and Lean error recovery left `sorryAx` in the theorem's axiom
list. The superfluous `ring` is removed; nothing else in the proof body
changed.

Only paid declarations are applied; nothing from the paid cluster is
re-proved:

* L1 (`deps/L1ForwardCarrier.lean`, read-only):
  `GammaPath_eq_coarseGammaPath_one_map` — the fine `GammaPath` IS the
  forward-tagged unit `coarseGammaPath 1` list;
  `unitSitesOf_one_image_eq_blockOf` — the `unitSitesOf 1 (1*ell) c.1`
  subtype carrier images EXACTLY onto `blockOf c.1 ell`.
* L2 (`deps/L2LineIntegralBridge.lean`, read-only):
  `dirDeriv_map_true_one_eq_lineIntegral` — at transport `1`,
  `dirDeriv V0 A c.1 ((coarseGammaPath 1 c.1 x).map (·,true)) 1`
  IS the coerced raw near-tree `lineIntegral 1 V0 (fineDirToUnitBond …)`;
  `fineDirToUnitBond` itself (`Aunit`).
* L6 (`deps/L6FittedSums.lean`, read-only, fitted under §4's hypotheses):
  `logData_Z_eq_ubarBracket` — the coefficient package's CARDINALITY MEAN
  `LogData.Z (sourcePrincipalLogData 1 ell V0) c'` IS the raw
  `w = ell⁻³`-weighted `ubarBracket` package `Z`; used ONLY for the operator
  `G`, never as a substitute for a summand weight.
* raw noloop stage (`deps/RawUbarDerivNoLoop.lean`, read-only):
  `qsmul_eq_rsmul` — `((ell:ℚ)^3)⁻¹ • X = ((ell:ℝ)^3)⁻¹ • X`.
* base package: `AdalyFormal.Balaban.QjComposite.stepBlockOf_one`
  (`stepBlockOf c.1 1 ell = blockOf c.1 ell`).

Proof route (raw `ell⁻³` weight throughout; no fitted cardinality mean is
substituted for a summand weight, no `Dcomputed` claim, no single-channel
claim):

1. `hsc`: real scalar algebra `(ell:ℝ) * (1/(ell:ℝ)^4) = ((ell:ℝ)^3)⁻¹`
   from `0 < ell` — the `ell⁻⁴`-normalized `term2` rescaled by `(ell:ℝ)`
   carries exactly the raw `ell⁻³` weight.
2. `hZ`: by paid L6, the corrected coefficient's `LogData.Z` at `c'` IS the
   raw weighted bracket package; `hZx`: the site log data is DEFINITIONALLY
   the raw principal loop log (`c'.1.1 = c.1`, `c'.2 = c.2`).
3. `hE1`: unfolding the corrected `Coeff124.ofPrincipalBackground`'s own
   `E1` field through the (uncorrected) `ofBackground` body and rewriting
   the two logarithm packages by step 2 gives
   `coeff.E1 c' x = G * P x - 1` with the RAW operators — this is the
   NEXT.md §5 spelling `E1_x = G * P_x - 1`, after the fitted raw-Z bridge,
   not a commutation.
4. `hsite`/`hA`: per site, `GammaPath` unfolds to the tagged unit staircase
   (L1), so `dirDeriv … 1 = ↑(tau x)` (L2), the ℚ/ℝ weights agree
   (`qsmul_eq_rsmul`), and the conjugated endpoint sum `Aminus` is
   `-↑(∑ w • tau x)` by skew-Hermiticity of the `SuTwo` sum.
5. `hB`: `Btau`'s carrier `stepBlockOf c.1 1 ell` IS `blockOf c.1 ell`
   (base-package `stepBlockOf_one`).
6. `hR'`: `(ell:ℝ) • term2` unfolds, rescales by `hsc`, distributes the
   weight into the sum, and reindexes from the `unitSitesOf` subtype carrier
   onto `blockOf c.1 ell` (L1) — giving the `w • coeff.E1 c' x (tau x)` sum.
7. Close: `-↑S_tau + ↑S_GP = ↑(S_GP - S_tau) = ↑(∑ w • E1_x(tau x))` by
   `Finset.sum_sub_distrib`, `smul_sub`, and the CLM split
   `(G * P x - 1) (tau x) = G (P x (tau x)) - tau x`.

No `W_x ≠ -I` premise is needed: no exp/log recovery, no `P_x Ad_{W_x} = N_x`
is invoked at this channel. No `sorry`, no placeholder, no assumed target.
-/
import Ch1Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch1Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp gOp gInvOp term2)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-1 PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch1Contract.Channel1Target`: every quantifier (arbitrary extent,
nonflat background, anti-Hermitian traceless field, block factor, fine edge)
and exactly the three NEXT.md fitting premises, no others. -/
theorem channel1_Aminus_add_Btau : AdalySI1.Ch1Contract.Channel1Target := by
  intro L V0 A hah htr ell c hcell hell hdvd
  -- the target's own literal coarse cast, abstracted once for reuse
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) scalar algebra: `(ell:ℝ) • ell⁻⁴ = ell⁻³`, needing only `0 < ell`.
  have h0 : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hsc : (ell : ℝ) * (1 / (ell : ℝ) ^ 4) = ((ell : ℝ) ^ 3)⁻¹ := by
    field_simp
  -- (2) the fitted raw-Z bridge (paid L6) and the definitional site logs.
  have hZ : OneStep124.LogData.Z (sourcePrincipalLogData 1 ell V0) c'
      = (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo) :=
    logData_Z_eq_ubarBracket hdvd V0 c'
  have hZx : ∀ x : PeriodicLatticeSite L,
      (sourcePrincipalLogData 1 ell V0).Zx c' x
        = principalSuTwoLog (loopVar 1 ell V0 c x) :=
    fun x => rfl
  -- (3) `E1_x = G * P_x - 1` at the corrected coefficient, raw operators.
  have hE1 : ∀ x : PeriodicLatticeSite L,
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
        = gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
          * gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))) - 1 := by
    intro x
    show gOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Z c')))
        * gInvOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Zx c' x))) - 1 = _
    rw [hZ, hZx x]
  -- (4) the endpoint sum `Aminus` is `-↑(∑ w • tau x)`.
  have hsite : ∀ x : PeriodicLatticeSite L,
      ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
          (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1
        = ((ell : ℝ) ^ 3)⁻¹ •
          ((lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (coarseGammaPath 1 c.1 x) : SuTwo) : M2) := by
    intro x
    rw [AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul,
      GammaPath_eq_coarseGammaPath_one_map,
      dirDeriv_map_true_one_eq_lineIntegral]
  have hA : (∑ x ∈ blockOf c.1 ell,
        ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
          (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1)ᴴ
      = -((∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x) : SuTwo) : M2) := by
    have hsum : (∑ x ∈ blockOf c.1 ell,
          ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
            (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1)
        = ((∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
              lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (coarseGammaPath 1 c.1 x) : SuTwo) : M2) := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl (fun x _ => by
        rw [Submodule.coe_smul]
        exact hsite x)
    rw [hsum]
    generalize (∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
      lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
        (coarseGammaPath 1 c.1 x) : SuTwo) = S
    exact S.2.1
  -- (5) `Btau`'s carrier is the same `blockOf c.1 ell`.
  have hB : ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x))) : SuTwo) : M2)
      = ((∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x))) : SuTwo) : M2) := by
    rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]
  -- (6) `(ell:ℝ) • ↑term2` is the coerced `w • E1_x(tau x)` block sum.
  have hR' : (ell : ℝ) •
        (term2 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo)
      = ∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x)) := by
    show (ell : ℝ) • ((1 / (ell : ℝ) ^ 4) •
        ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' u.1
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 u.1)))
      = _
    rw [smul_smul, hsc, Finset.smul_sum,
      ← unitSitesOf_one_image_eq_blockOf c.1 ell,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  have hR : (ell : ℝ) •
        ((term2 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo) : M2)
      = ((∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x)) : SuTwo) : M2) := by
    rw [← Submodule.coe_smul, hR']
  -- (7) per-site CLM split and the SuTwo sum identity.
  have happ : ∀ x : PeriodicLatticeSite L,
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (coarseGammaPath 1 c.1 x))
        = gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (coarseGammaPath 1 c.1 x)))
          - lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x) := by
    intro x
    rw [hE1 x, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply]
  have hpoint : ∀ x : PeriodicLatticeSite L,
      ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (coarseGammaPath 1 c.1 x)))
        - ((ell : ℝ) ^ 3)⁻¹ •
          lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (coarseGammaPath 1 c.1 x)
      = ((ell : ℝ) ^ 3)⁻¹ •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (coarseGammaPath 1 c.1 x)) := by
    intro x
    rw [happ x, smul_sub]
  have hfin : (∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (coarseGammaPath 1 c.1 x)))
        - ∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (coarseGammaPath 1 c.1 x) : SuTwo)
      = ∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1 c' x
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (coarseGammaPath 1 c.1 x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => hpoint x)
  -- (8) assemble.
  rw [hA, hB, hR, ← hfin, Submodule.coe_sub]
  abel

#print axioms channel1_Aminus_add_Btau

-- Fresh existence/axiom receipts for the exact paid declarations this proof applies.
#print axioms logData_Z_eq_ubarBracket
#print axioms unitSitesOf_one_image_eq_blockOf
#print axioms GammaPath_eq_coarseGammaPath_one_map
#print axioms dirDeriv_map_true_one_eq_lineIntegral
#print axioms AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul
#print axioms AdalyFormal.Balaban.QjComposite.stepBlockOf_one

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Ch1Proof.channel1_Aminus_add_Btau,
      `logData_Z_eq_ubarBracket,
      `unitSitesOf_one_image_eq_blockOf,
      `GammaPath_eq_coarseGammaPath_one_map,
      `dirDeriv_map_true_one_eq_lineIntegral,
      `AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul,
      `AdalyFormal.Balaban.QjComposite.stepBlockOf_one] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing channel-1 declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in channel-1 declaration {name}: {ax}"
  for mod in [`Ch1Target, `L2LineIntegralBridge, `L6FittedSums, `L1ForwardCarrier,
      `T1MainSegment, `RawUbarDerivNoLoop, `IngredientDeriv, `RawAverageDeriv,
      `AdalyFormal.Balaban.QjComposite, `AdalyFormal.Balaban.ThirdLevelArrows,
      `AdalyFormal.Balaban.AdmissibleSubspace, `AdalyFormal.Balaban.TowerLawCovariant] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"CH1_RESOLVED {mod}: {path}"
  Lean.logInfo "CH1_PROOF_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.Ch1Proof
