/-
CHANNEL 4 PROOF — pays the exact `AdalySI1.Ch4Contract.Channel4Target`
frozen in `ch4/Ch4Target.lean` (NEXT.md §5.4). Owned directory:
compute/m1_si1_asm2/ch4/. Authored in this owned directory; proof idioms
mirror the audited channel-1 and channels-2/3 proofs at
compute/m1_si1_asm2/ch1/Ch1Proof.lean and compute/m1_si1_asm2/ch23/Ch23Proof.lean
(same runner, same paid dependency cluster, same standard-axiom fence).

Only paid declarations are applied; nothing from the paid cluster is
re-proved:

* L5 (`deps/L5Proof.lean`, read-only, source SHA-256
  `4195f01661b42d4114f6ec49a171fede8385ad09063454f2d60b25655f33aba9`,
  matching the parent-verified l5audit pin):
  `AdalySI1.L5Proof.far_path_bridge` — for every actual block site
  `x ∈ stepBlockOf c.1 1 ell`, the ordered partner-path LIST equality
  `coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' x)
    = coarseGammaPath 1 c.1 x`, used to identify term4's partner-path
  integral with the raw `phiRaw x` (NEXT.md §5.4's required L5 use).
* L6 (`deps/L6FittedSums.lean`, read-only, fitted under §4's hypotheses):
  `partner_bijOn_blockOf` — fitted reindexing `partner c' : B_- ≃ B_+`
  between `blockOf c.1 ell` and `blockOf (OneStep124.cPlus c') ell`
  (NEXT.md §5.4's required L6 use);
  `logData_Z_eq_ubarBracket` — the coefficient package's CARDINALITY MEAN
  `LogData.Z (sourcePrincipalLogData 1 ell V0) c'` IS the raw
  `w = ell⁻³`-weighted `ubarBracket` package `Z`; used ONLY for the
  operators `G` and `Jminus`, never as a substitute for a summand weight.
* L1 (`deps/L1ForwardCarrier.lean`, read-only):
  `GammaPath_eq_coarseGammaPath_one_map` — the fine `GammaPath` IS the
  forward-tagged unit `coarseGammaPath 1` list (at the far base point);
  `cPlus_oneStep124_eq_cPlusS` and
  `cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus` — the coarse-cast
  `OneStep124.cPlus c'` IS `cPlusS 1 ell c` and IS
  `ModifiedAverageDeriv.cPlus ell c`;
  `unitSitesOf_one_image_eq_blockOf` — the `unitSitesOf 1 (1*ell) c.1`
  subtype carrier images EXACTLY onto `blockOf c.1 ell`.
* L2 (`deps/L2LineIntegralBridge.lean`, read-only):
  `dirDeriv_map_true_one_eq_lineIntegral` — at transport `1`,
  `dirDeriv … (GammaPath …) 1` IS the coerced raw line integral at the far
  base point; `fineDirToUnitBond` itself (`Aunit`).
* base packages: `AdalyFormal.Balaban.QjComposite.stepBlockOf_one`
  (`stepBlockOf c.1 1 ell = blockOf c.1 ell`);
  `AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply`
  (`(RMap U X : M2) = (U : M2) * (X : M2) * (U : M2)ᴴ` — the blocked-`K`
  sandwich, used as-is; `K` is never commuted past any operator);
  `AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul` (ℚ/ℝ weight agreement).

Proof route (raw `ell⁻³` weight throughout; no fitted cardinality mean is
substituted for a summand weight; no `Dcomputed` claim; no single-channel
claim; no commutation of operators from different backgrounds/logarithms;
identity-loop sites admitted, no exp/log recovery):

1. `hsc`: real scalar algebra `(ell:ℝ) * (1/(ell:ℝ)^4) = ((ell:ℝ)^3)⁻¹`
   from `0 < ell` — the `ell⁻⁴`-normalized `term4` rescaled by `(ell:ℝ)`
   carries exactly the raw `ell⁻³` weight.
2. `hZ` (paid L6) and the definitional site logs `hZx` give `hE2`:
   `coeff.E2 c' x = G * N x * Jminus - 1` with RAW operators — the NEXT.md
   §5 spelling after the fitted raw-Z bridge, not a commutation. Per site,
   `happ`: `G (N x (Jminus v)) = coeff.E2 c' x v + v` by the CLM split.
3. term4 side: `(ell:ℝ) • term4` unfolds at the corrected coefficient
   (whose `gbar c'` is definitionally `ubarSU2 1 ell V0 c = K`), rescales by
   `hsc`, reindexes from the `unitSitesOf` subtype carrier onto
   `blockOf c.1 ell` (paid L1), and per site the partner path is the raw
   near-tree path (paid L5) and the q-side base `OneStep124.cPlus c'` IS
   `cPlusS 1 ell c` (paid L1) — giving
   `(ell:ℝ) • term4 = -(∑ x∈blockOf c.1 ell, w • coeff.E2 c' x (RMap K
     (phiRaw x)))` in `SuTwo`.
4. `Bfar` side: `stepBlockOf_one` identifies the carriers; `happ` per site
   and `Finset.sum_add_distrib` give the raw `SuTwo` split
   `Bsum = (∑ w • E2_x (RMap K (phiRaw x))) + (∑ w • RMap K (phiRaw x))`.
5. `Cplus` side: per site, paid L1/L2 turn the `dirDeriv` endpoint summand
   into the raw-weight coerced line integral at the far base; the sum lifts
   through the `SuTwo → M2` coercion; the blocked `K`-sandwich IS
   `RMap K` (paid `RMap_coe_apply`); `RMap K` distributes over the weighted
   sum (`map_sum`, `map_smul`); the far-block carrier and base re-express
   through `OneStep124.cPlus c'` (paid L1); paid L6's `partner_bijOn_blockOf`
   reindexes the far-block sum back onto `blockOf c.1 ell`; paid L5 then
   turns each partner path into the raw near-tree path and paid L1 turns
   the base into `cPlusS 1 ell c` — so `Cplus = ↑(∑ x∈blockOf c.1 ell,
   w • RMap K (phiRaw x))` with `K` still in adjoint position.
6. Assemble in `M2`: `-(↑(SE2 + SR)) + ↑SR = -↑SE2 = ↑(-SE2)
   = ↑(ell • term4) = ell • ↑term4` by `Submodule.coe_add`,
   `Submodule.coe_smul`, `Submodule.coe_neg`, and `abel`.

No `W_x ≠ -I` premise is needed. No `sorry`, no placeholder, no assumed
target.
-/
import Ch4Target
import L5Proof
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch4Proof

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar cPlusS)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.DeltaKR66 (principalSuTwoLog sourcePrincipalLogData)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp term4 partner)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-4 PAYMENT.** Inhabitant of the frozen
`AdalySI1.Ch4Contract.Channel4Target` (NEXT.md §5.4): every quantifier
(arbitrary extent, nonflat background, anti-Hermitian traceless field, block
factor, fine edge) and exactly the three NEXT.md fitting premises, no
others. -/
theorem channel4_Bfar_add_Cplus : AdalySI1.Ch4Contract.Channel4Target := by
  intro L V0 A hah htr ell c hcell hell hdvd
  -- the target's own literal coarse cast, abstracted once for reuse
  set c' : CoarseBond L (1 * ell) := ⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ with hc'
  -- (1) scalar algebra: `(ell:ℝ) • ell⁻⁴ = ell⁻³`, needing only `0 < ell`.
  have h0 : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hsc : (ell : ℝ) * (1 / (ell : ℝ) ^ 4) = ((ell : ℝ) ^ 3)⁻¹ := by
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
  -- (2b) `E2_x = G * N_x * Jminus - 1` at the corrected coefficient, raw
  -- operators (the NEXT.md §5 spelling after the fitted raw-Z bridge).
  have hE2 : ∀ x : PeriodicLatticeSite L,
      (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' x
        = gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
          * gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          * expOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo))) - 1 := by
    intro x
    show gOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Z c')))
        * gInvOp (adOp ((sourcePrincipalLogData 1 ell V0).Zx c' x))
        * expOp (-(adOp ((sourcePrincipalLogData 1 ell V0).Z c'))) - 1 = _
    rw [hZ, hZx x]
  -- (2c) per-site CLM split: `G (N_x (Jminus v)) = coeff.E2 c' x v + v`.
  have happ : ∀ x : PeriodicLatticeSite L, ∀ v : SuTwo,
      gOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
          ubarBracket_trace V0 ell c⟩ : SuTwo)))
        (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
          (expOp (-(adOp (⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo))) v))
      = (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' x v + v := by
    intro x v
    rw [hE2 x, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, sub_add_cancel]
  -- (3a) the paid partner-list L5 bridge, instantiated at this stage's `c'`.
  have hL5 : ∀ x : PeriodicLatticeSite L, x ∈ stepBlockOf c.1 1 ell →
      coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' x)
        = coarseGammaPath 1 c.1 x :=
    fun x hx => AdalySI1.L5Proof.far_path_bridge ell c hcell hell hdvd x hx
  -- (3b) the paid L1 base-point identifications, at this stage's `c'`.
  have hcp : OneStep124.cPlus c' = cPlusS 1 ell c :=
    cPlus_oneStep124_eq_cPlusS ell c hcell
  have hcp2 : OneStep124.cPlus c' = AdalySI1.ModifiedAverageDeriv.cPlus ell c :=
    cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus ell c hcell
  -- (3c) the paid L6 fitted bijection `partner c' : B_- ≃ B_+`.
  have hbij := partner_bijOn_blockOf hell hdvd c'
  -- (4a) `(ell:ℝ) • term4` unfolds at the corrected coefficient (whose
  -- `gbar c'` is definitionally `ubarSU2 1 ell V0 c`) and rescales by `hsc`.
  have hT4 : (ell : ℝ) •
        (term4 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo)
      = -(∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
          ((ell : ℝ) ^ 3)⁻¹ •
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' u.1
              (RMap (ubarSU2 1 ell V0 c)
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                  (OneStep124.cPlus c')
                  (coarseGammaPath 1 (OneStep124.cPlus c')
                    (OneStep124.partner c' u.1))))) := by
    show (ell : ℝ) • (-((1 / (ell : ℝ) ^ 4) •
        ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c.1,
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' u.1
            (RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                (OneStep124.cPlus c')
                (coarseGammaPath 1 (OneStep124.cPlus c')
                  (OneStep124.partner c' u.1))))))
      = _
    rw [smul_neg, smul_smul, hsc, Finset.smul_sum]
  -- (4b) reindex onto the raw block; per site, paid L5 turns the partner
  -- path into the raw near-tree path and paid L1 the base into `cPlusS`.
  have hT4' : (ell : ℝ) •
        (term4 1 ell V0
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
          (fineDirToUnitBond A hah htr) c' : SuTwo)
      = -(∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' x
            (RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x)))) := by
    rw [hT4, ← unitSitesOf_one_image_eq_blockOf c.1 ell,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    show ((ell : ℝ) ^ 3)⁻¹ •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' u.1
          (RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (OneStep124.cPlus c')
              (coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' u.1))))
      = ((ell : ℝ) ^ 3)⁻¹ •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' u.1
          (RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
              (coarseGammaPath 1 c.1 u.1)))
    have hmem : u.1 ∈ blockOf c.1 ell := by
      rw [← unitSitesOf_one_image_eq_blockOf c.1 ell]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hx2 : u.1 ∈ stepBlockOf c.1 1 ell := by
      rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]
      exact hmem
    rw [hL5 u.1 hx2, hcp]
  -- (5) the raw `Bfar` sum splits into the `E2` mean plus the plain
  -- adjoint-`K` mean, over the raw block.
  have hB : (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
              (expOp (-(adOp (⟨ubarBracket V0 ell c,
                  ubarBracket_conjTranspose V0 ell c,
                  ubarBracket_trace V0 ell c⟩ : SuTwo)))
                (RMap (ubarSU2 1 ell V0 c)
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                    (coarseGammaPath 1 c.1 x))))) : SuTwo)
      = (∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E2 c' x
            (RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x))))
        + (∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x)) : SuTwo) := by
    rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by rw [happ x _, smul_add])
  -- (6a) per site, the `Cplus` endpoint summand is the raw-weight coerced
  -- line integral at the far base point (paid L1 path map, paid L2 bridge).
  have hsiteC : ∀ y : PeriodicLatticeSite L,
      ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A
          (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
          (AdalyFormal.Balaban.Q1Real.GammaPath
            (AdalySI1.ModifiedAverageDeriv.cPlus ell c) y) 1
        = ((ell : ℝ) ^ 3)⁻¹ •
          ((lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) y)
            : SuTwo) : M2) := by
    intro y
    rw [AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul,
      GammaPath_eq_coarseGammaPath_one_map,
      dirDeriv_map_true_one_eq_lineIntegral]
  -- (6b) the `Cplus` inner sum lifts through the `SuTwo → M2` coercion.
  have hsumC : (∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
        ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A
          (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
          (AdalyFormal.Balaban.Q1Real.GammaPath
            (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x) 1)
      = ((∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
            ((ell : ℝ) ^ 3)⁻¹ •
              lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
                (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x)
          : SuTwo) : M2) := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [Submodule.coe_smul]
      exact hsiteC x)
  -- (6c) the adjoint `K`-transport distributes over the weighted far sum.
  have hR1 : RMap (ubarSU2 1 ell V0 c)
        (∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x))
      = ∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
                (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun x _ => map_smul _ _ _)
  -- (6d) re-express the far carrier and base through `OneStep124.cPlus c'`.
  have hR2 : (∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
        ((ell : ℝ) ^ 3)⁻¹ •
          RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x)))
      = ∑ x ∈ blockOf (OneStep124.cPlus c') ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                (OneStep124.cPlus c')
                (coarseGammaPath 1 (OneStep124.cPlus c') x)) := by
    rw [← hcp2]
  -- (6e) paid L6 fitted reindexing of the far-block sum back onto `B_-`.
  have hR3 : (∑ x ∈ blockOf (OneStep124.cPlus c') ell,
        ((ell : ℝ) ^ 3)⁻¹ •
          RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (OneStep124.cPlus c')
              (coarseGammaPath 1 (OneStep124.cPlus c') x)))
      = ∑ x ∈ blockOf c.1 ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
                (OneStep124.cPlus c')
                (coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' x))) := by
    exact (Finset.sum_nbij (OneStep124.partner c')
      (fun a ha => Finset.mem_coe.mp (hbij.1 (Finset.mem_coe.mpr ha)))
      hbij.2.1 hbij.2.2 (fun a _ => rfl)).symm
  -- (6f) per site, paid L5 turns the partner path into the raw near-tree
  -- path and paid L1 turns the base into `cPlusS 1 ell c`.
  have hR4 : (∑ x ∈ blockOf c.1 ell,
        ((ell : ℝ) ^ 3)⁻¹ •
          RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (OneStep124.cPlus c')
              (coarseGammaPath 1 (OneStep124.cPlus c') (OneStep124.partner c' x))))
      = ∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
              (coarseGammaPath 1 c.1 x)) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx2 : x ∈ stepBlockOf c.1 1 ell := by
      rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]
      exact hx
    rw [hL5 x hx2, hcp]
  -- (6g) the whole `Cplus` endpoint IS the coerced adjoint-`K` raw mean.
  have hChain : RMap (ubarSU2 1 ell V0 c)
        (∑ x ∈ blockOf (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            lineIntegral 1 V0 (fineDirToUnitBond A hah htr)
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (coarseGammaPath 1 (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x))
      = ∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          RMap (ubarSU2 1 ell V0 c)
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
              (coarseGammaPath 1 c.1 x)) :=
    hR1.trans (hR2.trans (hR3.trans hR4))
  have hC : ((ubarSU2 1 ell V0 c : SU2) : M2)
        * (∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
            ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (AdalyFormal.Balaban.Q1Real.GammaPath
                (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x) 1)
        * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ
      = ((∑ x ∈ blockOf c.1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            RMap (ubarSU2 1 ell V0 c)
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                (coarseGammaPath 1 c.1 x)) : SuTwo) : M2) := by
    rw [hsumC]
    exact (AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply _ _).symm.trans
      (congrArg (fun s : SuTwo => (s : M2)) hChain)
  -- (7) assemble: `-(↑(SE2 + SR)) + ↑SR = -↑SE2 = ↑(ell • term4)`.
  rw [hC, hB, Submodule.coe_add]
  rw [← Submodule.coe_smul, hT4', Submodule.coe_neg]
  abel

#print axioms channel4_Bfar_add_Cplus

-- Fresh existence/axiom receipts for the exact paid declarations this proof applies.
#print axioms AdalySI1.L5Proof.far_path_bridge
#print axioms partner_bijOn_blockOf
#print axioms logData_Z_eq_ubarBracket
#print axioms unitSitesOf_one_image_eq_blockOf
#print axioms GammaPath_eq_coarseGammaPath_one_map
#print axioms cPlus_oneStep124_eq_cPlusS
#print axioms cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus
#print axioms dirDeriv_map_true_one_eq_lineIntegral
#print axioms AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul
#print axioms AdalyFormal.Balaban.QjComposite.stepBlockOf_one
#print axioms AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Ch4Proof.channel4_Bfar_add_Cplus,
      `AdalySI1.L5Proof.far_path_bridge,
      `partner_bijOn_blockOf,
      `logData_Z_eq_ubarBracket,
      `unitSitesOf_one_image_eq_blockOf,
      `GammaPath_eq_coarseGammaPath_one_map,
      `cPlus_oneStep124_eq_cPlusS,
      `cPlus_oneStep124_eq_modifiedAverageDeriv_cPlus,
      `dirDeriv_map_true_one_eq_lineIntegral,
      `AdalySI1.RawUbarDerivNoLoop.qsmul_eq_rsmul,
      `AdalyFormal.Balaban.QjComposite.stepBlockOf_one,
      `AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing channel-4 declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in channel-4 declaration {name}: {ax}"
  for mod in [`Ch4Target, `L5Proof, `C1Target, `L2LineIntegralBridge, `L6FittedSums,
      `L1ForwardCarrier, `L1CPlusBridge, `T1MainSegment, `RawUbarDerivNoLoop,
      `IngredientDeriv, `RawAverageDeriv, `ModifiedAverageDeriv,
      `AdalyFormal.Balaban.QjComposite, `AdalyFormal.Balaban.ThirdLevelArrows,
      `AdalyFormal.Balaban.AdmissibleSubspace, `AdalyFormal.Balaban.TowerLawCovariant,
      `AdalyFormal.Balaban.UbarTowerCovariance,
      `AdalyFormal.Balaban.CovariantOperators,
      `AdalyFormal.Balaban.BlockedBackground] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"CH4_RESOLVED {mod}: {path}"
  Lean.logInfo "CH4_PROOF_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.Ch4Proof
