#!/usr/bin/env python3
"""Restore the accepted radius-cofinal charged-leading assembly source.

The R1 file contains every physical and goal declaration used by the wrappers.
No earlier source is edited and no AHP module is imported.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/assembly/r1/AreaGoal.lean"
OUT = ROOT / "AHP/round15/assembly/r2/AreaGoal.lean"
PUBLISHED = ROOT / "AHP/round15/shared/assembly/R2_AreaGoal.lean"
REPORT = ROOT / "AHP/round15/assembly/r2/BUILD.json"

FOOTER = r'''

/-! Round 15 assembly R2: only cofinally many radii are needed at each
selected dyadic scale.  The physical identification remains an explicit input. -/
namespace AdalyFormal.Round15.Assembly

open AdalyFormal.Round2.Guarded.Pin (GoalNeg2)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
open AdalyFormal.Round13.Detection.PhysicalArea (areaSum)

/-- Charged-leading matrix data together with a generator/area identification
on arbitrarily large radius indices.  Unlike R1's ChargedLeadingData, this does
not require an identification at every natural index. -/
def CofinalRadiusChargedLeadingData (q : ℕ) (hq : 0 < q) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (r : ℝ) (K : ℕ → ι → ι → ℝ)
    (K0 : ι → ι → ℝ) (z : ι → ℂ),
    AdalyFormal.Round15.Seed.ChargedLeadingMatrix r K K0 z ∧
    ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
      ∃ u : TwistSpace q (2*(n+9)),
        KernelLine q (2*(n+9)) (rightStar hq (2*(n+9))) u ∧ ‖u‖ = 1 ∧
        ∃ k : ℕ, ∃ hk : k < blockCount q (2*(n+9)),
          areaSum hq hk u = AdalyFormal.Round14.Cancellation.chargedArea (K n) z

/-- The fixed-scale area family required by the nested physical seed. -/
def CofinalRadiusAreaSeed (q : ℕ) (hq : 0 < q) : Prop :=
  ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount q R, areaSum hq hk u ≠ 0

/-- Every all-index charged-leading identification is in particular a
cofinal-radius identification. -/
theorem cofinalRadiusChargedLeadingData_of_chargedLeading
    {q : ℕ} {hq : 0 < q}
    (h : AdalyFormal.Round15.Seed.ChargedLeadingData q hq) :
    CofinalRadiusChargedLeadingData q hq := by
  obtain ⟨ι, hι, r, K, K0, z, hmatrix, hident⟩ := h
  refine ⟨ι, hι, r, K, K0, z, hmatrix, ?_⟩
  intro n₀
  obtain ⟨u, hline, hnorm, k, hk, harea⟩ := hident n₀
  exact ⟨n₀, le_rfl, u, hline, hnorm, k, hk, harea⟩

/-- A nonzero normalized matrix limit supplies eventual nonvanishing, while
the physical dictionary supplies the same generator at arbitrarily large
indices.  Their intersection gives arbitrarily large admissible radii. -/
theorem cofinalRadiusAreaSeed_of_cofinalRadiusChargedLeadingData
    {q : ℕ} {hq : 0 < q}
    (h : CofinalRadiusChargedLeadingData q hq) :
    CofinalRadiusAreaSeed q hq := by
  obtain ⟨ι, hι, r, K, K0, z, hmatrix, hident⟩ := h
  letI := hι
  obtain ⟨hr, hz, hK0, hK⟩ := hmatrix
  have hev : ∀ᶠ n in atTop,
      AdalyFormal.Round14.Cancellation.chargedArea (K n) z ≠ 0 :=
    AdalyFormal.Round14.Cancellation.chargedArea_eventually_ne_zero_of_matrix_limit
      hr z hK0 hK
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  intro R₀
  obtain ⟨n, hn, u, hline, hnorm, k, hk, harea⟩ := hident (max N R₀)
  have hnN : N ≤ n := (le_max_left N R₀).trans hn
  have hnR : R₀ ≤ n := (le_max_right N R₀).trans hn
  refine ⟨2*(n+9), by omega, ⟨n+9, by ring⟩, by omega,
    u, hline, k, hk, ?_⟩
  rw [harea]
  exact hN n hnN

/-- Only cofinally many dyadic scales, and at each one cofinally many radii,
are required by this charged-leading certificate. -/
def CofinalRadiusChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    CofinalRadiusChargedLeadingData (2^j) (by positivity)

/-- The R1 nested certificate is a strengthening of the new radius-cofinal one. -/
theorem cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading
    (h : CofinalChargedLeadingCertificate) :
    CofinalRadiusChargedLeadingCertificate := by
  intro j₀
  obtain ⟨j, hj, hdata⟩ := h j₀
  exact ⟨j, hj, cofinalRadiusChargedLeadingData_of_chargedLeading hdata⟩

/-- The radius-cofinal charged-leading certificate gives the original nested
existential area seed, with every choice made at the same scale and radius. -/
theorem cofinalAreaSeed_of_cofinalRadiusChargedLeading
    (h : CofinalRadiusChargedLeadingCertificate) :
    AdalyFormal.Round14.Transfer.Physical.CofinalAreaSeedRightStar := by
  intro j₀
  obtain ⟨j, hj, hdata⟩ := h j₀
  refine ⟨j, hj, ?_⟩
  simpa only [CofinalRadiusAreaSeed] using
    (cofinalRadiusAreaSeed_of_cofinalRadiusChargedLeadingData hdata)

/-- Complete conditional chain from the weakened charged-leading input. -/
theorem goalNeg2_of_cofinalRadiusChargedLeading
    (h : CofinalRadiusChargedLeadingCertificate) : GoalNeg2 :=
  goalNeg2_of_cofinalAreaSeed (cofinalAreaSeed_of_cofinalRadiusChargedLeading h)

#print axioms CofinalRadiusChargedLeadingData
#print axioms CofinalRadiusAreaSeed
#print axioms cofinalRadiusChargedLeadingData_of_chargedLeading
#print axioms cofinalRadiusAreaSeed_of_cofinalRadiusChargedLeadingData
#print axioms CofinalRadiusChargedLeadingCertificate
#print axioms cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading
#print axioms cofinalAreaSeed_of_cofinalRadiusChargedLeading
#print axioms goalNeg2_of_cofinalRadiusChargedLeading
#check @CofinalRadiusChargedLeadingData
#check @CofinalRadiusAreaSeed
#check @cofinalRadiusChargedLeadingData_of_chargedLeading
#check @cofinalRadiusAreaSeed_of_cofinalRadiusChargedLeadingData
#check @CofinalRadiusChargedLeadingCertificate
#check @cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading
#check @cofinalAreaSeed_of_cofinalRadiusChargedLeading
#check @goalNeg2_of_cofinalRadiusChargedLeading

end AdalyFormal.Round15.Assembly
'''


def main() -> None:
    text = BASE.read_text() + FOOTER
    OUT.parent.mkdir(parents=True, exist_ok=True)
    PUBLISHED.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    PUBLISHED.write_text(text)
    report = {
        "base": str(BASE.relative_to(ROOT)),
        "output": str(OUT.relative_to(ROOT)),
        "published": str(PUBLISHED.relative_to(ROOT)),
        "lines": len(text.splitlines()),
        "sha256": hashlib.sha256(text.encode()).hexdigest(),
        "byteIdenticalPublication": OUT.read_bytes() == PUBLISHED.read_bytes(),
        "mainDeclaration": "AdalyFormal.Round15.Assembly.goalNeg2_of_cofinalRadiusChargedLeading",
        "boundary": "Conditional assembly only; no charged-leading physical dictionary or seed is supplied.",
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
