/-
CHANNEL 5 PROOF — pays the exact `AdalySI1.Ch5Contract.Channel5Target`
frozen in `ch5/Ch5Target.lean` (NEXT.md §5.5). Owned directory:
compute/m1_si1_asm2/ch5/. Authored in this owned directory; proof idioms
mirror the audited channel-1, channels-2/3 and channel-4 proofs at
compute/m1_si1_asm2/ch1/Ch1Proof.lean, compute/m1_si1_asm2/ch23/Ch23Proof.lean
and compute/m1_si1_asm2/ch4/Ch4Proof.lean (same runner, same paid dependency
cluster, same standard-axiom fence).

Only paid declarations are applied; nothing from the paid cluster is
re-proved:

* L6 (`deps/L6FittedSums.lean`, read-only, fitted under §4's hypotheses):
  `e3_ofBackground_eq_w_mean` — the SEPARATE E3-weight conversion named by
  NEXT.md §4 and required by §5.5: `Coeff124.ofBackground`'s own `E3` field
  (whose inner operator mean carries the source's `ν = |B_-|⁻¹` cardinality
  weight) IS the same inner mean reweighted by the fixed raw `w = ell⁻³`.
  This is NOT channel 2's mean equality and is not implied by it; it is
  applied here at `D = sourcePrincipalLogData 1 ell V0` and `c'`.
  `logData_Z_eq_ubarBracket` — the coefficient package's CARDINALITY MEAN
  `LogData.Z (sourcePrincipalLogData 1 ell V0) c'` IS the raw
  `w = ell⁻³`-weighted `ubarBracket` package `Z`; used ONLY for the
  operators `G` and `Jplus`, never as a substitute for a summand weight.
* L1 (`deps/L1ForwardCarrier.lean`, read-only):
  `unitSitesOf_one_image_eq_blockOf` — the `unitSitesOf 1 (1*ell) c.1`
  subtype carrier images EXACTLY onto `blockOf c.1 ell` (reindexing the E3
  inner operator mean onto the raw block).
* base package: `AdalyFormal.Balaban.QjComposite.stepBlockOf_one`
  (`stepBlockOf c.1 1 ell = blockOf c.1 ell`).

Proof route (raw `ell⁻³` weight throughout; no fitted cardinality mean is
substituted for a summand weight; no `Dcomputed` claim; no single-channel
claim; no commutation of operators from different backgrounds/logarithms;
identity-loop sites admitted, no exp/log recovery):

1. `hsc`: real scalar algebra `(ell:ℝ) * (1/(ell:ℝ)) = 1` from `0 < ell` —
   the `ell⁻¹`-normalized `term5` rescaled by `(ell:ℝ)` drops its
   normalization entirely (NEXT.md §5: "term5's `ell⁻¹`").
2. `hZ` (paid L6) and the definitional site logs `hZx`; then `hE3`: the
   SEPARATE paid L6 `e3_ofBackground_eq_w_mean` conversion, rewritten by
   `hZ`/`hZx`, gives the NEXT.md §5 spelling
   `coeff.E3 c' = Jplus - G * (Σ u∈unitSitesOf 1 (1*ell) c.1, w • N_u)`
   with RAW operators at the corrected principal coefficient record (whose
   `E3` field is definitionally `ofBackground`'s).
3. `hreindex`: paid L1 images the `unitSitesOf` subtype carrier onto
   `blockOf c.1 ell`; `stepBlockOf_one` identifies the carriers — `hE3'`
   is the same E3 spelling over the literal raw `S = stepBlockOf c.1 1 ell`.
4. `hGsum`: the head operator `G` distributes over the raw-weighted inner
   operator mean applied to `d` (`ContinuousLinearMap.sum_apply`,
   `map_sum`, per-site `smul_apply`/`map_smul`), giving the literal raw
   `Bdirect` sum `Σ x∈S, w • G (N x d)`.
5. `happly`: `coeff.E3 c' d = Jplus d - Σ x∈S, w • G (N x d)` by the CLM
   split (`sub_apply`, `mul_apply`) and `hGsum`.
6. `hT5`: `(ell:ℝ) • term5` unfolds (`term5 = ell⁻¹ • E3 c' d`) and rescales
   by `hsc` to `coeff.E3 c' d`.
7. Assemble in `M2`: `-↑Bsum + ↑(Jplus d) = ↑(-Bsum + Jplus d)
   = ↑(ell • term5) = ell • ↑term5` via `Submodule.coe_neg`,
   `Submodule.coe_add`, the `SuTwo` equality `key` (from `happly`, `hT5`),
   and `Submodule.coe_smul`. `Bout` stays positive, unweighted, outside the
   sum throughout.

No `W_x ≠ -I` premise is needed. No `sorry`, no placeholder, no assumed
target.
-/
import Ch5Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch5Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp term5)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-5 PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch5Contract.Channel5Target` (NEXT.md §5.5): every quantifier
(arbitrary extent, nonflat background, anti-Hermitian traceless field, block
factor, fine edge) and exactly the three NEXT.md fitting premises, no
others. -/
theorem channel5_Bdirect_add_Bout : AdalySI1.Ch5Contract.Channel5Target := by
  intro L V0 A hah htr ell c hcell hell hdvd
  -- the target's own literal coarse cast, abstracted once for reuse
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) scalar algebra: `(ell:ℝ) • ell⁻¹ = 1`, needing only `0 < ell`.
  have h0 : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hsc : (ell : ℝ) * (1 / (ell : ℝ)) = 1 := by
    field_simp
  -- (2a) the fitted raw-Z bridge (paid L6) and the definitional site logs.
  have hZ : OneStep124.LogData.Z (sourcePrincipalLogData 1 ell V0) c'
      = (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo) :=
    logData_Z_eq_ubarBracket hdvd V0 c'
  have hZx : ∀ x : PeriodicLatticeSite L,
      (sourcePrincipalLogData 1 ell V0).Zx c' x
        = principalSuTwoLog (loopVar 1 ell V0 c x) :=
    fun x => rfl
  -- (2b) the SEPARATE E3-weight conversion (paid L6): the corrected
  -- coefficient's `E3` field, converted from its own cardinality-weighted
  -- inner mean to the fixed raw `w = ell⁻³` inner mean, then rewritten by
  -- the fitted raw-Z bridge — the NEXT.md §5 spelling `E3 = Jplus - G *
  -- (Σ w • N_x)` with RAW operators, at the SAME background and logarithm.
  have hE3 : (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E3 c'
      = expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo))
        - gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          * (∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
              ((ell : ℝ) ^ 3)⁻¹ •
                gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c u.1)))
              : SuTwo →L[ℝ] SuTwo) := by
    have hconv := e3_ofBackground_eq_w_mean hdvd V0 (sourcePrincipalLogData 1 ell V0) c'
    rw [hZ] at hconv
    simp only [hZx] at hconv
    rw [one_div] at hconv
    exact hconv
  -- (3) reindex the inner operator mean onto the raw block (paid L1), then
  -- identify `stepBlockOf c.1 1 ell` with it (base package).
  have hreindex : (∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
        ((ell : ℝ) ^ 3)⁻¹ •
          gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c u.1)))
        : SuTwo →L[ℝ] SuTwo)
      = ∑ x ∈ blockOf c.1 ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x))) := by
    rw [← unitSitesOf_one_image_eq_blockOf c.1 ell,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  have hE3' : (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E3 c'
      = expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo))
        - gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          * (∑ x ∈ stepBlockOf c.1 1 ell,
              ((ell : ℝ) ^ 3)⁻¹ •
                gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
              : SuTwo →L[ℝ] SuTwo) := by
    rw [hE3, hreindex, ← AdalyFormal.Balaban.QjComposite.stepBlockOf_one]
  -- (4) the head operator `G` distributes over the raw-weighted inner
  -- operator mean applied to the direct segment `d`.
  have hGsum : gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo)))
        ((∑ x ∈ stepBlockOf c.1 1 ell,
            ((ell : ℝ) ^ 3)⁻¹ •
              gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
            : SuTwo →L[ℝ] SuTwo)
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (List.replicate ell c.2)))
      = ∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (List.replicate ell c.2))) := by
    rw [ContinuousLinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [ContinuousLinearMap.smul_apply, map_smul])
  -- (5) the CLM split applied to `d`: `coeff.E3 c' d = Jplus d - Σ w • G (N x d)`.
  have happly : (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E3 c'
        (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
          (List.replicate ell c.2))
      = expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (List.replicate ell c.2))
        - ∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
                ubarBracket_trace V0 ell c⟩ : SuTwo)))
              (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (List.replicate ell c.2))) := by
    rw [hE3', ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, hGsum]
  -- (6) `(ell:ℝ) • term5` unfolds at the corrected coefficient
  -- (`term5 = ell⁻¹ • E3 c' d`) and rescales by `hsc`.
  have hT5 : (ell : ℝ) •
        (term5 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo)
      = (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E3 c'
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (List.replicate ell c.2)) := by
    show (ell : ℝ) • ((1 / (ell : ℝ)) •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E3 c'
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
            (List.replicate ell c.2)))
      = _
    rw [smul_smul, hsc, one_smul]
  -- (7a) the raw `SuTwo` assembly: `-Bsum + Jplus d = (ell:ℝ) • term5`.
  have key : (-(∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (List.replicate ell c.2))))
        + expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) : SuTwo)
      = (ell : ℝ) •
        (term5 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo) := by
    rw [hT5, happly]
    abel
  -- (7b) assemble in `M2`: `-↑Bsum + ↑(Jplus d) = ↑(-Bsum + Jplus d)
  -- = ↑(ell • term5) = ell • ↑term5`. `Bout` stays positive, unweighted,
  -- and outside the weighted sum.
  calc (-((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
              gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
                  ubarBracket_trace V0 ell c⟩ : SuTwo)))
                (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                    (List.replicate ell c.2)))) : SuTwo) : M2)
        + ((expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (List.replicate ell c.2)) : SuTwo) : M2)
        = ((-((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
                gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
                    ubarBracket_trace V0 ell c⟩ : SuTwo)))
                  (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
                    (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                      (List.replicate ell c.2)))))
            + expOp (adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
                ubarBracket_trace V0 ell c⟩ : SuTwo))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (List.replicate ell c.2)) : SuTwo) : M2) := by
          rw [Submodule.coe_add, Submodule.coe_neg]
      _ = (((ell : ℝ) •
            (term5 1 ell V0
              (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
              (fineDirToUnitBond A hah htr) c' : SuTwo)) : M2) :=
          congrArg (fun s : SuTwo => (s : M2)) key
      _ = (ell : ℝ) •
          ((term5 1 ell V0
              (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
              (fineDirToUnitBond A hah htr) c' : SuTwo) : M2) :=
          Submodule.coe_smul _ _

#print axioms channel5_Bdirect_add_Bout

-- Fresh existence/axiom receipts for the exact paid declarations this proof applies.
#print axioms e3_ofBackground_eq_w_mean
#print axioms logData_Z_eq_ubarBracket
#print axioms unitSitesOf_one_image_eq_blockOf
#print axioms AdalyFormal.Balaban.QjComposite.stepBlockOf_one

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Ch5Proof.channel5_Bdirect_add_Bout,
      `e3_ofBackground_eq_w_mean,
      `logData_Z_eq_ubarBracket,
      `unitSitesOf_one_image_eq_blockOf,
      `AdalyFormal.Balaban.QjComposite.stepBlockOf_one] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing channel-5 declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in channel-5 declaration {name}: {ax}"
  for mod in [`Ch5Target, `L2LineIntegralBridge, `L6FittedSums, `L1ForwardCarrier,
      `T1MainSegment, `RawUbarDerivNoLoop,
      `AdalyFormal.Balaban.QjComposite, `AdalyFormal.Balaban.ThirdLevelArrows,
      `AdalyFormal.Balaban.AdmissibleSubspace,
      `AdalyFormal.Balaban.UbarTowerCovariance,
      `AdalyFormal.Balaban.CovariantOperators] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"CH5_RESOLVED {mod}: {path}"
  Lean.logInfo "CH5_PROOF_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.Ch5Proof
