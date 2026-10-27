/-
CHANNELS 2 AND 3 CONTRACT ONLY: executable propositions, NOT proofs.
Owned directory: compute/m1_si1_asm2/ch23/. Authored in this owned directory
(no draft origin); statement shapes mirror the audited channel-1 contract at
compute/m1_si1_asm2/ch1/Ch1Target.lean, with the NEXT.md §2 raw dictionary
verbatim from compute/m1_si1_c3_gated/spec/C3Target.lean (SHA-256
41c67fa83bc14b74d7a588937f1ae5b0c0724ac5ae358c47c8c5b1621a40d008, verified
read-only in compute/m1_si1_c3_gated/audit/C3Target.lean).

Freezes the exact second and third channel obligations of
`compute/m1_si1_c3_gated/audit/NEXT.md` §5.2/§5.3, plus the explicit
`Bsigma` split NEXT.md §5 demands alongside them:

    (2) ↑(Σ x∈S, w • sigma x)
          = (ell : ℝ) • ↑(unitToCoarseCov 1 ell V0 Aunit c')
    (3) ↑(Σ x∈S, w • coeff.E1 c' x (sigma x))
          = (ell : ℝ) • ↑(OneStep124.term3 1 ell V0 coeff Aunit c')
    split: Bsigma = ↑(Σ x∈S, w • sigma x) + ↑(Σ x∈S, w • coeff.E1 c' x (sigma x))

with the NEXT.md §2 raw dictionary, verbatim:

* `S := stepBlockOf c.1 1 ell`, `w : ℝ := ((ell : ℝ)^3)⁻¹` (the RAW weight —
  never the cardinality mean `|S|⁻¹`, which is not substituted anywhere);
* `q x := coarseGammaPath 1 c.1 x`, `r := List.replicate ell c.2`;
* `sigma x := RMap (coarsePathHolonomy 1 V0 c.1 (q x))
    (lineIntegral 1 V0 Aunit x r)` — the literal shifted-segment raw leaf of
  `AdalySI1.C3Contract.C3Point`, tree holonomy on the OUTSIDE;
* `Z := ⟨ubarBracket V0 ell c, ubarBracket_conjTranspose V0 ell c,
    ubarBracket_trace V0 ell c⟩` — the literal raw weighted bracket (not a
  cardinality mean, not a principal log of `K`), `Zx x := principalSuTwoLog
    (loopVar 1 ell V0 c x)`;
* `G := gOp (-(adOp Z))`, `P x := gInvOp (-(adOp (Zx x)))` — raw operators;
  `Bsigma := ((∑ x∈S, w • G (P x (sigma x)) : SuTwo) : M2)`, exactly C3's
  second raw leaf;
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
Identity-loop sites need no `W_x ≠ -I` cut at these channels: no exp/log
recovery is invoked.

Not asserted here: channels 1, 4, 5 (channel 1 is paid separately in
compute/m1_si1_asm2/ch1/), the partner-list L5 substitution, any
`Dcomputed =` identity (single-channel or five-channel), boxed SI1, CMP98
analyticity / Fréchet regularity / quadratic remainder / five-channel source
match. Elaboration of these propositions is not a proof of them.
-/
import L2LineIntegralBridge
import L6FittedSums
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.Ch23Contract

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
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.RawUbarDerivNoLoop
  (ubarBracket ubarBracket_conjTranspose ubarBracket_trace)
open OneStep124 (lineIntegral adOp gOp gInvOp term3)

variable {L : PeriodicLatticeExtent}

/-- **THE CHANNEL-2 ACCEPTANCE TARGET** (NEXT.md §5.2). The coerced raw plain
`sigma` mean over the literal `S = stepBlockOf c.1 1 ell` with the raw
`ell⁻³` weight IS the `(ell : ℝ)`-rescaled coercion of the actual main-term
`unitToCoarseCov 1 ell V0 Aunit c'` (CMP98's (125) channel T1). -/
def Channel2Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)),
    ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
          (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
            (List.replicate ell c.2)) : SuTwo) : M2)
      = (ell : ℝ) •
        ((unitToCoarseCov 1 ell V0 (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

/-- **THE CHANNEL-3 ACCEPTANCE TARGET** (NEXT.md §5.3). The coerced raw
`E1`-mean of `sigma` over the literal `S` with the raw `ell⁻³` weight IS the
`(ell : ℝ)`-rescaled coercion of `OneStep124.term3 1 ell V0 coeff Aunit c'`,
with the CORRECTED principal coefficient record. -/
def Channel3Target : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)),
    ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell)) x
          (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
            (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
              (List.replicate ell c.2))) : SuTwo) : M2)
      = (ell : ℝ) •
        ((term3 1 ell V0
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0)
            (fineDirToUnitBond A hah htr)
            (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2)

/-- **THE EXPLICIT `Bsigma` SPLIT** (NEXT.md §5: "split `Bsigma` into the
plain sigma mean plus its E1 mean"). C3's literal second raw leaf
`Bsigma = ↑(Σ x∈S, w • G (P x (sigma x)))` IS the plain `sigma` mean PLUS the
`E1`-mean of `sigma`, both coerced to `M2`. The per-site identity behind it is
`G (P x s) = s + coeff.E1 c' x s`, i.e. the NEXT.md §5 spelling
`E1_x = G * P_x - 1` with the RAW operators `G`, `P_x` — available only after
the fitted raw-Z bridge (paid L6 `logData_Z_eq_ubarBracket`), and used here
pointwise at the SAME site with the SAME raw `Z`, never as a commutation of
operators from different backgrounds or logarithms. -/
def BsigmaSplitTarget : Prop :=
  ∀ {L : PeriodicLatticeExtent}
    (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)),
    ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        gOp (-(adOp (⟨ubarBracket V0 ell c,
            ubarBracket_conjTranspose V0 ell c,
            ubarBracket_trace V0 ell c⟩ : SuTwo)))
          (gInvOp (-(adOp (principalSuTwoLog (loopVar 1 ell V0 c x))))
            (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                (List.replicate ell c.2)))) : SuTwo) : M2)
      = ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
              (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                (List.replicate ell c.2)) : SuTwo) : M2)
        + ((∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell V0).E1
              (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell)) x
              (RMap (coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x))
                (lineIntegral 1 V0 (fineDirToUnitBond A hah htr) x
                  (List.replicate ell c.2))) : SuTwo) : M2)

#print Channel2Target
#print Channel3Target
#print BsigmaSplitTarget
#print axioms Channel2Target
#print axioms Channel3Target
#print axioms BsigmaSplitTarget

end AdalySI1.Ch23Contract
