#!/usr/bin/env python3
"""Build the round-2 assembly from the published R2 transfer/cancellation work.

Only files under assembly/r2 and (with --publish) shared/assembly are written.
The input sources are read, never edited.  No physical seed is asserted.
"""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
TRANSFER = ROOT / "AHP/round14/transfer/r2/Collar.lean"
CANCELLATION = ROOT / "AHP/round14/cancellation/r2/AreaStructure.lean"
MARKER = "/-! Round 14 cancellation R2: exact U(1) line structure for the genuine area,"
TARGET = HERE / "AreaLine.lean"
PUBLISHED = ROOT / "AHP/round14/shared/assembly/R2_AreaLine.lean"

APPEND = r'''

/-!
Assembly R2: turn one area-detected generator into the universal area
remainder, directly at the level of `areaSum`.  This uses the cancellation
track's exact charged-span theorem.  No physical area seed is supplied.
-/
namespace AdalyFormal.Round14.Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
open AdalyFormal.Round13.Detection.PhysicalArea

/-- The original universal area remainder from assembly R1. -/
def AreaNonvanishing : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0

/-- One detected generator gives nonzero area for EVERY nonzero vector on the
same original KernelLine.  The proof stays at the area level: the exact
U(1)-affine area formula replaces the response-gradient argument. -/
theorem areaNonvanishing_of_areaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) :
    AreaNonvanishing := by
  intro q R hq hR hR18 v hv
  obtain ⟨u, hline, j, hj, harea⟩ := h hq hR hR18
  refine ⟨j, hj, ?_⟩
  exact AdalyFormal.Round14.Cancellation.areaSum_ne_zero_of_mem_charged_span
    hq hj harea (hline.2.2.2 v hv.2.1) hv.1

/-- The unit-full-norm formulation is likewise sufficient for the universal
area remainder; normalization is not confused with nine-bond normalization. -/
theorem areaNonvanishing_of_unitAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar) :
    AreaNonvanishing :=
  areaNonvanishing_of_areaSeed
    (AdalyFormal.Round14.Transfer.Physical.unitAreaSeedRightStar_iff.mp h)

/-- The already compiled area-to-curl bridge from assembly R1. -/
theorem p3_of_areaNonvanishing (h : AreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R1.P3 := by
  intro q R hq hR hR18 u hline
  exact crossing_curlDetected_of_area hq hR hR18 (rightStar hq R) u hline
    (h hq hR hR18 u hline)

/-- Consolidated conditional route: one area seed implies the original P3 via
the universal area remainder.  This is not an inhabitant of the seed or P3. -/
theorem p3_of_areaSeed_via_area
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3 :=
  p3_of_areaNonvanishing (areaNonvanishing_of_areaSeed h)

/-- The normalized R2 seed gives the same conditional conclusion. -/
theorem p3_of_unitAreaSeed_via_area
    (h : AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3 :=
  p3_of_areaNonvanishing (areaNonvanishing_of_unitAreaSeed h)

#print axioms AreaNonvanishing
#print axioms areaNonvanishing_of_areaSeed
#print axioms areaNonvanishing_of_unitAreaSeed
#print axioms p3_of_areaNonvanishing
#print axioms p3_of_areaSeed_via_area
#print axioms p3_of_unitAreaSeed_via_area
#check @AreaNonvanishing
#check @areaNonvanishing_of_areaSeed
#check @areaNonvanishing_of_unitAreaSeed
#check @p3_of_areaNonvanishing
#check @p3_of_areaSeed_via_area
#check @p3_of_unitAreaSeed_via_area

end AdalyFormal.Round14.Assembly
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    transfer = TRANSFER.read_text(encoding="utf-8")
    cancellation = CANCELLATION.read_text(encoding="utf-8")
    start = cancellation.index(MARKER)
    text = transfer + "\n\n" + cancellation[start:] + APPEND
    TARGET.write_text(text, encoding="utf-8")
    print(f"wrote {TARGET} ({len(text.splitlines())} lines)")
    if args.publish:
        PUBLISHED.parent.mkdir(parents=True, exist_ok=True)
        PUBLISHED.write_text(text, encoding="utf-8")
        print(f"wrote {PUBLISHED} (byte-identical)")


if __name__ == "__main__":
    main()
