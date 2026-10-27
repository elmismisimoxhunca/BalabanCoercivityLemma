/-
CHANNEL 4 CONTRACT ONLY: executable proposition, NOT a proof of channel 4.
Owned directory: compute/m1_si1_asm2/ch4/. Authored in this owned directory
(no draft origin); statement shape mirrors the audited channel-1 contract at
compute/m1_si1_asm2/ch1/Ch1Target.lean, with the NEXT.md §2 raw dictionary
verbatim from compute/m1_si1_c3_gated/spec/C3Target.lean (SHA-256
41c67fa83bc14b74d7a588937f1ae5b0c0724ac5ae358c47c8c5b1621a40d008, verified
read-only in compute/m1_si1_c3_gated/audit/C3Target.lean) and the `Cplus`
endpoint verbatim from the loaded product theorem
`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`
(deps/ProdFullAssembleDerivNoLoop.lean:108-111).

Freezes the exact fourth channel obligation of
`compute/m1_si1_c3_gated/audit/NEXT.md` §5.4:

    Bfar + Cplus = (ell : ℝ) • ↑(OneStep124.term4 1 ell V0 coeff Aunit c')

with the NEXT.md §2 raw dictionary, verbatim:

* `S := stepBlockOf c.1 1 ell`, `w : ℝ := ((ell : ℝ)^3)⁻¹` (the RAW weight —
  never the cardinality mean `|S|⁻¹`, which is not substituted anywhere);
* `q x := coarseGammaPath 1 c.1 x`;
* `Z := ⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
    ubarBracket_trace V0 ell c⟩` — the literal raw weighted bracket (not a
  cardinality mean, not a principal log of `K`);
  `Zx x := principalSuTwoLog (loopVar 1 ell V0 c x)`;
* `K := ubarSU2 1 ell V0 c` — the blocked background average, kept in its
  adjoint (sandwich) position throughout; no operator commutation;
* `phiRaw x := lineIntegral 1 V0 Aunit (cPlusS 1 ell c) (q x)` — the literal
  UNTRANSLATED raw far-list leaf of `AdalySI1.C3Contract.C3Point` (its base is
  `cPlusS 1 ell c`, its path the raw near-tree staircase `q x`);
* `G := gOp (-(adOp Z))`, `N x := gInvOp (adOp (Zx x))`,
  `Jminus := expOp (-(adOp Z))` — raw operators, acting rightmost first;
* `Bfar := -((∑ x∈S, w • G (N x (Jminus (RMap K (phiRaw x)))) : SuTwo) : M2)`,
  exactly C3's third raw leaf, retaining its outer negative sign;
* `Cplus := ((K : SU2) : M2) * (∑ x ∈ blockOf (ModifiedAverageDeriv.cPlus ell
    c) ell, ((ell : ℚ)^3)⁻¹ • dirDeriv V0 A (ModifiedAverageDeriv.cPlus ell c)
    (GammaPath (ModifiedAverageDeriv.cPlus ell c) x) 1) * ((K : SU2) : M2)ᴴ`,
  the literal second endpoint of the loaded product theorem, `K` blocked in
  adjoint position on both sides;
* `coeff := AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0`
  (the CORRECTED constructor, `gbar = ubarSU2 = K`, never the uncorrected
  `Coeff124.ofBackground` whose `gbar` is the direct bond holonomy `C`);
* `Aunit := fineDirToUnitBond A hah htr` (paid L2 packaging);
* `c' := (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1*ell))`,
  the NEXT.md §3 coarse cast.

The only premises are the three NEXT.md fitting hypotheses: `hcell` (coarse
alignment), `hell : 0 < ell`, `hdvd : ∀ μ, ell ∣ (L μ + 1)`. Arbitrary extent
`L`, arbitrary (generally nonflat) background `V0`, arbitrary anti-Hermitian
traceless direction field `A`, arbitrary block factor `ell` and fine edge `c`.
Identity-loop sites need no `W_x ≠ -I` cut at this channel: no exp/log
recovery is invoked.

Not asserted here: channels 1, 2, 3, 5 (paid separately), the `Bsigma` split,
any `Dcomputed =` identity (single-channel or five-channel
`Dcomputed = ell • ↑q124Principal`), boxed SI1, CMP98 analyticity / Fréchet
regularity / quadratic remainder / five-channel source match. Elaboration of
this proposition is not a proof of it.
-/
import L2LineIntegralBridge
import L6FittedSums
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch4Contract

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
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp term4)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-4 ACCEPTANCE TARGET** (NEXT.md §5.4). The raw `Bfar` leaf
(negative, weighted, `K` adjoint-wrapped around the untranslated raw
far-list line integral `phiRaw x = lineIntegral 1 V0 Aunit (cPlusS 1 ell c)
(coarseGammaPath 1 c.1 x)`) PLUS the literal `Cplus` endpoint of the loaded
product theorem (`K`-sandwiched far-block `dirDeriv` mean) IS the
`(ell : ℝ)`-rescaled coercion of `OneStep124.term4 1 ell V0 coeff Aunit c'`
at the CORRECTED principal coefficient record. -/
def Channel4Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)),
    (-((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          gOp (-(adOp (⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo)))
            (gInvOp (adOp (principalSuTwoLog (loopVar 1 ell V0 c x)))
              (expOp (-(adOp (⟨ubarBracket V0 ell c,
                  ubarBracket_conjTranspose V0 ell c,
                  ubarBracket_trace V0 ell c⟩ : SuTwo)))
                (RMap (ubarSU2 1 ell V0 c)
                  (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) (cPlusS 1 ell c)
                    (coarseGammaPath 1 c.1 x)))))) : SuTwo) : M2)
      + ((ubarSU2 1 ell V0 c : SU2) : M2)
        * (∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c) ell,
            ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A
              (AdalySI1.ModifiedAverageDeriv.cPlus ell c)
              (AdalyFormal.Balaban.Q1Real.GammaPath
                (AdalySI1.ModifiedAverageDeriv.cPlus ell c) x) 1)
        * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ
      = (ell : ℝ) •
        ((term4 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

#print Channel4Target
#print axioms Channel4Target

end AdalySI1.Ch4Contract
