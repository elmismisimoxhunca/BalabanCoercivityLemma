/-
FINAL FIVE-CHANNEL ASSEMBLY — pays
    Dcomputed = (ell : ℝ) • ↑(AdalyFormal.DeltaKR85.q124Principal 1 ell V0 Aunit c')
frozen as `AdalySI1.Asm3.DcomputedQ124Target` below (the final display of
`compute/m1_si1_c3_gated/audit/NEXT.md` §5). Owned directory:
compute/m1_si1_asm3/asm/.

`Dcomputed` is the LITERAL derivative value of the paid, loaded product theorem
`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`
(`deps/ProdFullAssembleDerivNoLoop.lean`): its three additive slots, verbatim —
`Aminus` (conjugated near endpoint block sum, `((ell:ℚ)^3)⁻¹`-weighted),
`slotB` (the raw ubar-slot), and `Cplus` (the `K`-adjoint-sandwiched far
endpoint block sum). Nothing is re-proved; only paid certificates are applied:

* C3 (`AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves`, the audited
  `compute/m1_si1_c3_gated/audit/C3Proof.lean`, SHA-256
  `61a5d08e27ca863345183e2c40269985bc7905b53a82244e3bf1bb32bf940bdb`,
  vendored byte-identical into this owned directory because the runner's
  extra `LEAN_PATH` roots are confined to `compute/m1_si1_asm3`):
  `slotB = Btau + Bsigma + Bfar + Bdirect + Bout`, the five raw leaves with
  `Bfar`/`Bdirect` negative and `Bout` positive, unweighted, outside the sum.
* The five certified channel equalities (NEXT.md §5.1–§5.5), applied, never
  re-proved: `Ch1Proof.channel1_Aminus_add_Btau`
  (`Aminus + Btau = (ell:ℝ) • ↑term2`), `Ch23Proof.channel2_sigma_mean`
  (plain `sigma` mean `= (ell:ℝ) • ↑unitToCoarseCov`),
  `Ch23Proof.channel3_E1_sigma_mean` (`E1`-mean of `sigma`
  `= (ell:ℝ) • ↑term3`), `Ch23Proof.bsigma_split_plain_add_E1`
  (`Bsigma =` plain mean `+` `E1`-mean), `Ch4Proof.channel4_Bfar_add_Cplus`
  (`Bfar + Cplus = (ell:ℝ) • ↑term4`), `Ch5Proof.channel5_Bdirect_add_Bout`
  (`Bdirect + Bout = (ell:ℝ) • ↑term5`). All at the CORRECTED coefficient
  `AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0`
  (`gbar = ubarSU2 = K`), all with the raw `ell⁻³` weight (never a
  cardinality mean).
* The paid T1 split (`deps/T1MainSegment.lean`)
  `AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta`:
  `q124Principal`'s own construction IS `unitToCoarseCov + delta124`, and
  `delta124` is by definition `term2 + term3 + term4 + term5`.

Premises: exactly the three NEXT.md fitting hypotheses `hcell` (coarse
alignment), `hell : 0 < ell`, `hdvd : ∀ μ, ell ∣ (L μ + 1)`, PLUS the paid
product theorem's and C3's own analytic premise `hnc2` (the blockwise
`loopVar ≠ su2NegOne` principal-log cut on the literal `S`) — no new geometry
premise is introduced; arbitrary (generally nonflat) `V0`, arbitrary
anti-Hermitian traceless `A`, arbitrary `ell`, `c`; identity-loop sites remain
admitted. No operator commutation, no single-channel `Dcomputed` claim, no
boxed SI1, no CMP98 analyticity/Fréchet/remainder claim.

Assembly route (pure additive algebra over `M2` after the paid payments):
  `Dcomputed = Aminus + (Btau + Bsigma + Bfar + Bdirect + Bout) + Cplus`  (C3)
  `= (Aminus + Btau) + Bsigma + (Bfar + Cplus) + (Bdirect + Bout)`        (abel)
  `= (ell:ℝ)•↑term2 + (↑plain + ↑E1sigma) + (ell:ℝ)•↑term4 + (ell:ℝ)•↑term5`
                                                                       (ch1, split, ch4, ch5)
  `= (ell:ℝ)•↑term2 + ((ell:ℝ)•↑u2c + (ell:ℝ)•↑term3) + …`              (ch2, ch3)
  `= (ell:ℝ) • ↑(u2c + term2 + term3 + term4 + term5)`              (coe/smul)
  `= (ell:ℝ) • ↑(q124Principal 1 ell V0 Aunit c')`                  (paid T1 split)

The second theorem transports the value equality onto the paid product
theorem's `HasDerivAt` (the same `hcongr`-style bridge the product file itself
uses), making `Dcomputed` honest: the actual derivative of
`modifiedAverage … (configMul (t • A) V0) …` at `t = 0` IS
`(ell:ℝ) • ↑q124Principal`.
-/
import Ch1Proof
import Ch23Proof
import Ch4Proof
import Ch5Proof
import C3Proof
import ProdFullAssembleDerivNoLoop
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Asm3

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov
  (coarseGammaPath coarsePathHolonomy unitToCoarseCov)
open AdalyFormal.Balaban.UbarTowerCov (loopVar cPlusS coarseBondVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage configMul)
open AdalySI1.RawAverageDeriv (holonomyDirDeriv)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp term2 term3 term4 term5)

variable {L : PeriodicLatticeExtent}

/-- **THE ASSEMBLY TARGET.** The literal three-slot derivative value
`Dcomputed = Aminus + slotB + Cplus` of the paid product theorem
`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`
(all three slots verbatim, including the ℚ-weighted `Aminus`/`Cplus` endpoints
and the raw ubar middle slot) IS the `(ell : ℝ)` scalar multiple of the
`M2`-coercion of the actual CMP98 (124) five-channel principal form
`AdalyFormal.DeltaKR85.q124Principal 1 ell V0 Aunit c'`, with
`Aunit = fineDirToUnitBond A hah htr` and the NEXT.md §3 coarse cast
`c' = (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))`.
Premises: the three fitting hypotheses plus the paid product/C3 analytic cut
`hnc2`; nothing else. -/
def DcomputedQ124Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne),
    ((∑ x ∈ blockOf c.1 ell,
          ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
            (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1)ᴴ
      + ((fderiv ℝ NormedSpace.exp (ubarBracket V0 ell c))
            (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
              deriv (fun t : ℝ =>
                su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
            * ((coarseBondVar 1 ell V0 c : SU2) : M2)
          + ((su2Exp (ubarBracket V0 ell c) : SU2) : M2)
            * holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))
        * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ
      + ((ubarSU2 1 ell V0 c : SU2) : M2)
        * (∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
            ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (AdalyFormal.Balaban.Q1Real.GammaPath
                (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x) 1)
        * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ)
      = (ell : ℝ) •
        ((AdalyFormal.DeltaKR85.q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

/-- **THE ASSEMBLY PAYMENT.** Inhabitant of the frozen
`AdalySI1.Asm3.DcomputedQ124Target`. Every ingredient is a paid certificate
applied verbatim; the only proof content is additive regrouping and the paid
T1 split of `q124Principal`. -/
theorem dcomputed_eq_ell_smul_q124Principal : DcomputedQ124Target := by
  intro L V0 A hah htr ell c hcell hell hdvd hnc2
  -- paid C3: the literal middle slot IS the five raw leaves. The equation is
  -- normalized out of `C3Point` by `unfold`/`dsimp` (the same normalization
  -- the audited C3 proof itself uses), so no leaf is hand-transcribed here.
  have hC3 := AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves V0 A hah htr ell c hnc2
  unfold AdalySI1.C3Contract.C3Point at hC3
  dsimp only at hC3
  -- the five certified channel equalities and the `Bsigma` split
  have h1 := AdalySI1.Ch1Proof.channel1_Aminus_add_Btau V0 A hah htr ell c hcell hell hdvd
  have h2 := AdalySI1.Ch23Proof.channel2_sigma_mean V0 A hah htr ell c hcell hell hdvd
  have h3 := AdalySI1.Ch23Proof.channel3_E1_sigma_mean V0 A hah htr ell c hcell hell hdvd
  have hbs := AdalySI1.Ch23Proof.bsigma_split_plain_add_E1 V0 A hah htr ell c hcell hell hdvd
  have h4 := AdalySI1.Ch4Proof.channel4_Bfar_add_Cplus V0 A hah htr ell c hcell hell hdvd
  have h5 := AdalySI1.Ch5Proof.channel5_Bdirect_add_Bout V0 A hah htr ell c hcell hell hdvd
  -- the paid T1 split: `q124Principal` IS `unitToCoarseCov + term2 + … + term5`.
  have hq : AdalyFormal.DeltaKR85.q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
        (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
      = unitToCoarseCov 1 ell V0 (fineDirToUnitBond A hah htr)
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
        + term2 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
        + term3 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
        + term4 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
        + term5 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell)) := by
    rw [AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta]
    unfold OneStep124.delta124
    abel
  -- additive regrouping of the seven displayed pieces (pure `M2` abelian algebra)
  have hgroup : ∀ a b1 b2 b3 b4 b5 cp : M2,
      a + ((((b1 + b2) + b3) + b4) + b5) + cp
        = (((a + b1) + b2) + (b3 + cp)) + (b4 + b5) := by
    intro a b1 b2 b3 b4 b5 cp
    abel
  -- assemble: substitute C3, regroup, apply the six channel payments, then
  -- collect the `(ell:ℝ)` scalar over the `SuTwo → M2` coercion and fold by hq.
  rw [hC3, hgroup, h1, hbs, h4, h5, h2, h3, hq]
  simp only [Submodule.coe_add, smul_add]
  abel

/-- **THE LOADED-PRODUCT BRIDGE.** The paid product theorem's actual
`HasDerivAt` conclusion, with its derivative value transported by the assembly
equality above: the derivative of CMP98 (89)/(63)'s four-factor
`modifiedAverage V0 ell (configMul (t • A) V0) c` at `t = 0`, coerced to `M2`,
IS `(ell : ℝ) • ↑(q124Principal 1 ell V0 Aunit c')`. Same premises as the
assembly target (no `h`-division; `h = 0` remains admissible downstream). -/
theorem hasDerivAt_modifiedAverage_coe_configMul_noloop_q124
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) :
    HasDerivAt (fun t : ℝ => ((modifiedAverage V0 ell (fun e => su2Exp (t • A e)) c : SU2) : M2))
      ((ell : ℝ) •
        ((AdalyFormal.DeltaKR85.q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)) 0 := by
  have hcongr : ∀ {f : ℝ → M2} {d1 d2 : M2}, d1 = d2 → HasDerivAt f d1 0 → HasDerivAt f d2 0 :=
    fun heq hd => heq ▸ hd
  exact hcongr (dcomputed_eq_ell_smul_q124Principal V0 A hah htr ell c hcell hell hdvd hnc2)
    (AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop
      V0 A hah htr ell c hnc2)

#print DcomputedQ124Target
#print axioms dcomputed_eq_ell_smul_q124Principal
#print axioms hasDerivAt_modifiedAverage_coe_configMul_noloop_q124

-- Fresh existence/axiom receipts for the exact paid certificates this stage applies.
#print axioms AdalySI1.Ch1Proof.channel1_Aminus_add_Btau
#print axioms AdalySI1.Ch23Proof.channel2_sigma_mean
#print axioms AdalySI1.Ch23Proof.channel3_E1_sigma_mean
#print axioms AdalySI1.Ch23Proof.bsigma_split_plain_add_E1
#print axioms AdalySI1.Ch4Proof.channel4_Bfar_add_Cplus
#print axioms AdalySI1.Ch5Proof.channel5_Bdirect_add_Bout
#print axioms AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves
#print axioms AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop
#print axioms AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.Asm3.dcomputed_eq_ell_smul_q124Principal,
      `AdalySI1.Asm3.hasDerivAt_modifiedAverage_coe_configMul_noloop_q124,
      `AdalySI1.Ch1Proof.channel1_Aminus_add_Btau,
      `AdalySI1.Ch23Proof.channel2_sigma_mean,
      `AdalySI1.Ch23Proof.channel3_E1_sigma_mean,
      `AdalySI1.Ch23Proof.bsigma_split_plain_add_E1,
      `AdalySI1.Ch4Proof.channel4_Bfar_add_Cplus,
      `AdalySI1.Ch5Proof.channel5_Bdirect_add_Bout,
      `AdalySI1.C3Proof.prod_slotB_eq_five_raw_leaves,
      `AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop,
      `AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing assembly declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in assembly declaration {name}: {ax}"
  for mod in [`Ch1Target, `Ch1Proof, `Ch23Target, `Ch23Proof, `Ch4Target, `Ch4Proof,
      `Ch5Target, `Ch5Proof, `C3Target, `C3Proof, `ProdFullAssembleDerivNoLoop,
      `T1MainSegment, `L6FittedSums, `L1ForwardCarrier, `L2LineIntegralBridge,
      `RawUbarDerivNoLoop, `IngredientDeriv, `ModifiedAverageDeriv] do
    let path ← Lean.findOLean mod
    Lean.logInfo m!"ASM3_RESOLVED {mod}: {path}"
  Lean.logInfo "ASM3_PROOF_PAID_DECLARATIONS_STANDARD_AXIOMS_PASS"

end AdalySI1.Asm3
