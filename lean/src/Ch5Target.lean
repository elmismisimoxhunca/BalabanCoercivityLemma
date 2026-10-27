/-
CHANNEL 5 CONTRACT ONLY: executable proposition, NOT a proof of channel 5.
Owned directory: compute/m1_si1_asm2/ch5/. Authored in this owned directory
(no draft origin; compute/m1_si1_assembly/ contains only ch1, deps, l5audit);
statement shape mirrors the audited channel-1, channels-2/3 and channel-4
contracts at compute/m1_si1_asm2/ch1/Ch1Target.lean,
compute/m1_si1_asm2/ch23/Ch23Target.lean and
compute/m1_si1_asm2/ch4/Ch4Target.lean, with the NEXT.md §2 raw dictionary
verbatim from compute/m1_si1_c3_gated/spec/C3Target.lean (SHA-256
41c67fa83bc14b74d7a588937f1ae5b0c0724ac5ae358c47c8c5b1621a40d008, verified
read-only in compute/m1_si1_c3_gated/audit/C3Target.lean).

Freezes the exact fifth channel obligation of
`compute/m1_si1_c3_gated/audit/NEXT.md` §5.5:

    Bdirect + Bout = (ell : ℝ) • ↑(OneStep124.term5 1 ell V0 coeff Aunit c')

with the NEXT.md §2 raw dictionary, verbatim:

* `S := stepBlockOf c.1 1 ell`, `w : ℝ := ((ell : ℝ)^3)⁻¹` (the RAW weight —
  never the cardinality mean `|S|⁻¹`, which is not substituted anywhere);
* `r := List.replicate ell c.2`;
* `d := lineIntegral 1 V0 Aunit c.1 r` — the literal direct-segment raw leaf
  of `AdalySI1.C3Contract.C3Point`;
* `Z := ⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
    ubarBracket_trace V0 ell c⟩` — the literal raw weighted bracket (not a
  cardinality mean, not a principal log of `K`);
  `Zx x := principalSuTwoLog (loopVar 1 ell V0 c x)`;
* `G := gOp (-(adOp Z))`, `N x := gInvOp (adOp (Zx x))`,
  `Jplus := expOp (adOp Z)` — raw operators, acting rightmost first;
* `Bdirect := -((∑ x∈S, w • G (N x d) : SuTwo) : M2)`, exactly C3's fourth
  raw leaf, retaining its outer negative sign;
* `Bout := ((Jplus d : SuTwo) : M2)` — POSITIVE, unweighted, and outside the
  weighted sum; it is not optional;
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

Not asserted here: channels 1, 2, 3, 4 (paid separately), the `Bsigma`
split (paid in ch23), any `Dcomputed =` identity (no channel is claimed to
be the whole derivative; the single-channel and five-channel
`Dcomputed = ell • ↑q124Principal` identities remain open), boxed SI1,
CMP98 analyticity / Fréchet regularity / quadratic remainder / full
five-channel source match. Elaboration of this proposition is not a proof of
it.
-/
import L2LineIntegralBridge
import L6FittedSums
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch5Contract

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp expOp gOp gInvOp term5)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-5 ACCEPTANCE TARGET** (NEXT.md §5.5). The raw `Bdirect`
leaf (negative, weighted, raw operators `G`, `N x` applied rightmost-first to
the direct-segment line integral `d = lineIntegral 1 V0 Aunit c.1
(List.replicate ell c.2)`) PLUS the POSITIVE unweighted outside-the-sum
`Bout = ((Jplus d : SuTwo) : M2)` IS the `(ell : ℝ)`-rescaled coercion of
`OneStep124.term5 1 ell V0 coeff Aunit c'` at the CORRECTED principal
coefficient record. -/
def Channel5Target : Prop :=
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
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
                (List.replicate ell c.2)))) : SuTwo) : M2)
      + ((expOp (adOp (⟨ubarBracket V0 ell c,
              ubarBracket_conjTranspose V0 ell c,
              ubarBracket_trace V0 ell c⟩ : SuTwo))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) c.1
              (List.replicate ell c.2)) : SuTwo) : M2)
      = (ell : ℝ) •
        ((term5 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

#print Channel5Target
#print axioms Channel5Target

end AdalySI1.Ch5Contract
