/-
CHANNEL 1 CONTRACT ONLY: executable proposition, NOT a proof of channel 1.
Owned directory: compute/m1_si1_asm2/ch1/ (copied byte-identical except this
owned-directory line from compute/m1_si1_assembly/ch1/Ch1Target.lean, whose
SHA-256 was 7f3f44b3676e904f89b13325e8c64ce16593f21ef6e0b2ad2c784464db3196b0;
the proposition below is verbatim).

Freezes the exact first channel obligation of
`compute/m1_si1_c3_gated/audit/NEXT.md` §5.1:

    Aminus + Btau = (ell : ℝ) • ↑(OneStep124.term2 1 ell V0 coeff Aunit c')

with the NEXT.md §2 raw dictionary, verbatim:

* `Aminus` is the literal conjugated endpoint block sum as it occurs in the
  loaded product theorem
  `AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`
  (`deps/ProdFullAssembleDerivNoLoop.lean:96-99`), whole-sum conjugated,
  `((ell : ℚ)^3)⁻¹`-weighted, summed over `blockOf c.1 ell`;
* `Btau` is the literal first weighted raw leaf of `AdalySI1.C3Contract.C3Point`
  (`compute/m1_si1_c3_gated/spec/C3Target.lean`): `stepBlockOf c.1 1 ell` sum,
  raw weight `((ell : ℝ)^3)⁻¹`, operators
  `G := gOp (-(adOp Z))`, `P x := gInvOp (-(adOp (Zx x)))` with the RAW
  weighted bracket `Z = ⟨ubarBracket V0 ell c, …⟩` (not a cardinality mean and
  not a principal log of `K`) and `Zx x = principalSuTwoLog (loopVar 1 ell V0 c x)`,
  applied to the literal near-tree line integral
  `tau x = lineIntegral 1 V0 Aunit c.1 (coarseGammaPath 1 c.1 x)`;
* `coeff` is the CORRECTED constructor
  `AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0`
  (`gbar = ubarSU2 = K`), never the uncorrected `OneStep124.Coeff124.ofBackground`
  (whose `gbar` is the direct bond holonomy `C`);
* `Aunit = fineDirToUnitBond A hah htr` (paid L2 packaging);
* `c'` is the NEXT.md §3 coarse cast `(⟨c.1, …⟩, c.2) : CoarseBond L (1 * ell)`.

The only premises are the three fitting hypotheses NEXT.md names:
`c.1 ∈ CoarseLattice L ell`, `0 < ell`, and `∀ μ, ell ∣ (L μ + 1)`.
No `W_x ≠ -I` cut is needed at this channel: no exp/log recovery is invoked.
No channel 2–5, no `Dcomputed = ell • ↑q124Principal`, no boxed SI1 is asserted.
-/
import L2LineIntegralBridge
import L6FittedSums
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch1Contract

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp gOp gInvOp term2)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-1 ACCEPTANCE TARGET.** Arbitrary extent `L`, arbitrary
(generally nonflat) background `V0`, arbitrary anti-Hermitian traceless
direction field `A`, arbitrary block factor `ell` and fine edge `c`; premises
are exactly the three NEXT.md fitting hypotheses. The equality is the literal
NEXT.md §5.1 channel-1 display: raw `Aminus + Btau` on the left,
`(ell : ℝ) • ↑(term2 1 ell V0 coeff Aunit c')` with the corrected principal
coefficient on the right. -/
def Channel1Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)),
    (∑ x ∈ blockOf c.1 ell,
        ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
          (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1)ᴴ
      + ((∑ x ∈ stepBlockOf c.1 1 ell,
          ((ell : ℝ) ^ 3)⁻¹ •
            gOp (-(adOp (⟨ubarBracket V0 ell c,
                ubarBracket_conjTranspose V0 ell c,
                ubarBracket_trace V0 ell c⟩ : SuTwo)))
              (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                  (coarseGammaPath 1 c.1 x))) : SuTwo) : M2)
      = (ell : ℝ) •
        ((term2 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

#print Channel1Target
#print axioms Channel1Target

end AdalySI1.Ch1Contract
