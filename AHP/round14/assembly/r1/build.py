#!/usr/bin/env python3
"""Build the round-14 area/detection integration from the frozen round-13 copy.

Only AHP/round14/assembly/r1/AreaP3.lean is written.  The historical source is
read, never modified.  No theorem without a proof is introduced: the two area
propositions are explicit hypotheses of every implication proved here.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "AHP/round13/shared/detection/R2_PhysicalArea.lean"
TARGET = Path(__file__).resolve().parent / "AreaP3.lean"

APPEND = r'''

/-! Only the right-star definitions are added to the detection copy. -/
namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
variable {L : PeriodicLatticeExtent}

def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)

def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round12.Noncancel.Path

def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)
end AdalyFormal.Round12.Noncancel.RightFamily

set_option linter.unusedVariables false

/-! Original P3 predicate, copied verbatim from round-13 assembly R1. -/
namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)

def P3 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u

/-- Original existential detected-line predicate, copied verbatim from R1. -/
def CofinalRightStarCurlLine : Prop :=
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
end AdalyFormal.Round13.Assembly.R1

/-! Original weaker cofinal P3 predicate, copied verbatim from round-13 R2. -/
namespace AdalyFormal.Round13.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)

def CofinalP3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u
end AdalyFormal.Round13.Assembly.R2

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

/-- Exact all-instance physical area remainder.  This is a definition, not a
claimed inhabitant. -/
def AreaNonvanishing : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0

/-- Exact nested existential area family from the round-13 detection notes.
This too is only a predicate until a proof is supplied. -/
def CofinalAreaNonvanishing : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
        areaSum (by positivity : 0 < 2^j) hk u ≠ 0

/-- The proved area dictionary and flat-unit bridge reduce P3 exactly to the
all-instance area remainder. -/
theorem p3_of_areaNonvanishing (h : AreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R1.P3 := by
  intro q R hq hR hR18 u hline
  exact crossing_curlDetected_of_area hq hR hR18 (rightStar hq R) u hline
    (h hq hR hR18 u hline)

/-- The all-instance area remainder also supplies the weaker nested P3 form,
with the same indices at every step. -/
theorem cofinalP3_of_areaNonvanishing (h : AreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3 := by
  intro j₀
  refine ⟨j₀, le_rfl, ?_⟩
  intro R₀
  refine ⟨2 * (R₀ + 18), by omega, ⟨R₀ + 18, rfl⟩, by omega, ?_⟩
  intro u hline
  exact p3_of_areaNonvanishing h (by positivity) ⟨R₀ + 18, rfl⟩ (by omega) u hline

/-- The nested existential area family gives the original detected-line family;
no intersection of separately selected subsequences is used. -/
theorem cofinalRightStarCurlLine_of_cofinalAreaNonvanishing
    (h : CofinalAreaNonvanishing) :
    AdalyFormal.Round13.Assembly.R1.CofinalRightStarCurlLine := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, ?_⟩
  intro R₀
  obtain ⟨R, hR₀, hR, hR18, u, hline, k, hk, harea⟩ := hRs R₀
  refine ⟨R, hR₀, hR, hR18, u, hline, ?_⟩
  exact crossing_curlDetected_of_area (by positivity) hR hR18
    (rightStar (by positivity) R) u hline ⟨k, hk, harea⟩

#print axioms AdalyFormal.Round13.Assembly.R1.P3
#print axioms AdalyFormal.Round13.Assembly.R1.CofinalRightStarCurlLine
#print axioms AdalyFormal.Round13.Assembly.R2.CofinalP3
#print axioms AdalyFormal.Round14.Assembly.AreaNonvanishing
#print axioms AdalyFormal.Round14.Assembly.CofinalAreaNonvanishing
#print axioms AdalyFormal.Round14.Assembly.p3_of_areaNonvanishing
#print axioms AdalyFormal.Round14.Assembly.cofinalP3_of_areaNonvanishing
#print axioms AdalyFormal.Round14.Assembly.cofinalRightStarCurlLine_of_cofinalAreaNonvanishing
#check @AdalyFormal.Round14.Assembly.p3_of_areaNonvanishing
#check @AdalyFormal.Round14.Assembly.cofinalP3_of_areaNonvanishing
#check @AdalyFormal.Round14.Assembly.cofinalRightStarCurlLine_of_cofinalAreaNonvanishing
end AdalyFormal.Round14.Assembly
'''


def main() -> None:
    source = SOURCE.read_text()
    TARGET.write_text(source + APPEND, encoding="utf-8")
    print(f"wrote {TARGET} ({len((source + APPEND).splitlines())} lines)")


if __name__ == "__main__":
    main()
