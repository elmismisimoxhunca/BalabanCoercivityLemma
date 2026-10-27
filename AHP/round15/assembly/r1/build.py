#!/usr/bin/env python3
"""Build the round-15 area-seed-to-goal assembly without AHP imports.

The round-13 goal file is the base.  From the round-14 area file we append only
declarations whose fully-qualified names are not already present in that base.
All retained text is copied verbatim; no earlier-round file is modified.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round13/shared/assembly/R2_P2Goal.lean"
AREA = ROOT / "AHP/round14/shared/assembly/R2_AreaLine.lean"
SEED = ROOT / "AHP/round15/seed/r1/Seed.lean"
OUT = ROOT / "AHP/round15/assembly/r1/AreaGoal.lean"
PUBLISHED = ROOT / "AHP/round15/shared/assembly/R1_AreaGoal.lean"
REPORT = ROOT / "AHP/round15/assembly/r1/BUILD.json"

DECL = re.compile(
    r"^(?:@\[[^]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|inductive|structure|class|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*)"
)
NAMESPACE = re.compile(r"^namespace\s+(.+?)\s*$")
SECTION = re.compile(r"^section(?:\s+.*?)?\s*$")
END = re.compile(r"^end(?:\s+(.+?))?\s*$")
BOUNDARY = re.compile(
    r"^(?:namespace\b|section\b|end\b|open\b|variable\b|universe\b|"
    r"set_option\b|#print\b|#check\b|#eval\b|#reduce\b|attribute\b|"
    r"local\b|scoped\b|include\b|omit\b)"
)
MODIFIER = re.compile(r"^(?:set_option|include|omit|open)\b.*\bin$")
ATTRIBUTE = re.compile(r"^@\[.*\]$")


def declaration(lines: list[str], index: int, stack: list[tuple[str, str | None]]):
    match = DECL.match(lines[index])
    if not match:
        return None
    namespace = ".".join(item[1] for item in stack if item[0] == "ns")
    name = match.group(1)
    return (namespace + "." if namespace else "") + name


def declarations(path: Path) -> list[tuple[str, int]]:
    lines = path.read_text().splitlines()
    stack: list[tuple[str, str | None]] = []
    result = []
    for index, line in enumerate(lines):
        match = NAMESPACE.match(line)
        if match:
            stack.append(("ns", match.group(1)))
            continue
        if SECTION.match(line):
            stack.append(("sec", None))
            continue
        if END.match(line):
            if stack:
                stack.pop()
            continue
        name = declaration(lines, index, stack)
        if name:
            result.append((name, index + 1))
    return result


def filtered_source(path: Path, base_names: set[str]) -> tuple[str, dict]:
    lines = path.read_text().splitlines()
    stack: list[tuple[str, str | None]] = []
    kept: list[str] = []
    # Whether each kept line belongs to the removable comment/modifier prefix
    # of a following declaration.  Dropping a duplicate also drops that prefix,
    # which is essential for `omit ... in`, `include ... in`, and `open ... in`.
    removable: list[bool] = []
    dropped: list[tuple[str, int]] = []
    retained: list[tuple[str, int]] = []
    dropping = False
    in_comment = False

    for index, line in enumerate(lines):
        stripped = line.strip()
        comment_line = in_comment
        if in_comment:
            if "-/" in stripped:
                in_comment = False
        elif stripped.startswith("/-"):
            comment_line = True
            if "-/" not in stripped[2:]:
                in_comment = True
        elif stripped.startswith("--"):
            comment_line = True
        is_removable = (
            not stripped
            or comment_line
            or bool(MODIFIER.match(stripped))
            or bool(ATTRIBUTE.match(stripped))
        )

        # Imports are deliberately restricted to those already in the base.
        # Comments and audit-only commands from the input are not needed in the
        # compact merged source; the new footer prints all new goal arrows.
        if (line.startswith("import ") or comment_line
                or stripped.startswith("#print") or stripped.startswith("#check")):
            continue

        name = declaration(lines, index, stack)
        if dropping:
            if name is None and not BOUNDARY.match(line):
                continue
            dropping = False

        if name is not None:
            if name in base_names:
                dropped.append((name, index + 1))
                dropping = True
                while removable and removable[-1]:
                    removable.pop()
                    kept.pop()
                continue
            retained.append((name, index + 1))
            base_names.add(name)

        kept.append(line)
        removable.append(is_removable)

        match = NAMESPACE.match(line)
        if match:
            stack.append(("ns", match.group(1)))
        elif SECTION.match(line):
            stack.append(("sec", None))
        elif END.match(line) and stack:
            stack.pop()

    return "\n".join(kept), {
        "retainedDeclarations": retained,
        "droppedDuplicateDeclarations": dropped,
    }


FOOTER = r'''

/-! Round 15 assembly: the complete compiled conditional arrows from the
physical area inputs to the pinned negative goal.  No seed is inhabited here. -/
namespace AdalyFormal.Round15.Assembly

open AdalyFormal.Round2.Guarded.Pin (GoalNeg2)

/-- One same-generator nonzero physical area at every admissible instance
refutes the pinned guarded headline, via the compiled P3 bridge. -/
theorem goalNeg2_of_areaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3
    (AdalyFormal.Round14.Transfer.Physical.p3_of_areaSeed h)

/-- The unit-full-carrier-norm seed gives the same conditional conclusion. -/
theorem goalNeg2_of_unitAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.UnitAreaSeedRightStar) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3
    (AdalyFormal.Round14.Transfer.Physical.p3_of_unitAreaSeed h)

/-- The nested existential area family gives the pinned goal through CofinalP3. -/
theorem goalNeg2_of_cofinalAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.CofinalAreaSeedRightStar) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
    (AdalyFormal.Round14.Transfer.Physical.cofinalP3_of_areaSeed h)

/-- The exact three-term Laurent certificate is sufficient, conditionally. -/
theorem goalNeg2_of_laurentAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.CofinalLaurentAreaSeed) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
    (AdalyFormal.Round14.Transfer.Physical.cofinalP3_of_laurentAreaSeed h)

/-- A dominant normalized-limit certificate with arbitrary remainder suffices. -/
theorem goalNeg2_of_dominantAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.CofinalDominantAreaSeed) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
    (AdalyFormal.Round14.Transfer.Physical.cofinalP3_of_dominantAreaSeed h)

/-- The normalized unit-full-norm dominant certificate is the current preferred
cofinal interface.  Its physical input remains open. -/
theorem goalNeg2_of_unitDominantAreaSeed
    (h : AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed) : GoalNeg2 :=
  AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
    (AdalyFormal.Round14.Transfer.Physical.cofinalP3_of_unitDominantAreaSeed h)

/-- The seed track's fixed finite charged-leading data also closes the
conditional chain.  Its physical dictionary is not supplied by this theorem. -/
theorem goalNeg2_of_chargedLeading
    (h : AdalyFormal.Round15.Seed.DyadicChargedLeadingCertificate) : GoalNeg2 :=
  goalNeg2_of_unitDominantAreaSeed
    (AdalyFormal.Round15.Seed.cofinalUnitDominantAreaSeed_of_chargedLeading h)

/-- Only cofinally many dyadic charged-leading certificates are required.
Each chosen scale still needs the full even-radius progression. -/
def CofinalChargedLeadingCertificate : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    AdalyFormal.Round15.Seed.ChargedLeadingData (2^j) (by positivity)

/-- The nested charged-leading certificate implies the preferred dominant seed
without strengthening it to a certificate at every dyadic scale. -/
theorem cofinalUnitDominantAreaSeed_of_cofinalChargedLeading
    (h : CofinalChargedLeadingCertificate) :
    AdalyFormal.Round14.Transfer.Physical.CofinalUnitDominantAreaSeed := by
  intro j₀
  obtain ⟨j, hj, ι, hι, r, K, K0, z, hmatrix, hident⟩ := h j₀
  letI := hι
  refine ⟨j, hj, AdalyFormal.Round15.Seed.radiusChargedObservable K z,
    AdalyFormal.Round15.Seed.radiusDominantData_of_chargedLeadingMatrix hmatrix, ?_⟩
  intro n
  obtain ⟨u, hline, hnorm, k, hk, harea⟩ := hident n
  refine ⟨u, hline, hnorm, k, hk, ?_⟩
  rw [harea]
  have hidx : 2*(n+9)/2 - 9 = n := by omega
  simp only [AdalyFormal.Round15.Seed.radiusChargedObservable, hidx]

/-- The complete conditional chain from the nested charged-leading input. -/
theorem goalNeg2_of_cofinalChargedLeading
    (h : CofinalChargedLeadingCertificate) : GoalNeg2 :=
  goalNeg2_of_unitDominantAreaSeed
    (cofinalUnitDominantAreaSeed_of_cofinalChargedLeading h)

#print axioms goalNeg2_of_areaSeed
#print axioms goalNeg2_of_unitAreaSeed
#print axioms goalNeg2_of_cofinalAreaSeed
#print axioms goalNeg2_of_laurentAreaSeed
#print axioms goalNeg2_of_dominantAreaSeed
#print axioms goalNeg2_of_unitDominantAreaSeed
#print axioms goalNeg2_of_chargedLeading
#print axioms CofinalChargedLeadingCertificate
#print axioms cofinalUnitDominantAreaSeed_of_cofinalChargedLeading
#print axioms goalNeg2_of_cofinalChargedLeading
#check @goalNeg2_of_areaSeed
#check @goalNeg2_of_unitAreaSeed
#check @goalNeg2_of_cofinalAreaSeed
#check @goalNeg2_of_laurentAreaSeed
#check @goalNeg2_of_dominantAreaSeed
#check @goalNeg2_of_unitDominantAreaSeed
#check @goalNeg2_of_chargedLeading
#check @CofinalChargedLeadingCertificate
#check @cofinalUnitDominantAreaSeed_of_cofinalChargedLeading
#check @goalNeg2_of_cofinalChargedLeading

end AdalyFormal.Round15.Assembly
'''


def main() -> None:
    base_text = BASE.read_text()
    base_names = {name for name, _ in declarations(BASE)}
    addition, report = filtered_source(AREA, base_names)
    seed_addition, seed_report = filtered_source(SEED, base_names)
    text = (base_text
        + "\n\n/-! Round-14 physical area declarations, deduplicated verbatim. -/\n"
        + addition
        + "\n\n/-! Round-15 charged-leading declarations, deduplicated verbatim. -/\n"
        + seed_addition + FOOTER)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    PUBLISHED.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    PUBLISHED.write_text(text)
    report.update({
        "base": str(BASE.relative_to(ROOT)),
        "area": str(AREA.relative_to(ROOT)),
        "seed": str(SEED.relative_to(ROOT)),
        "seedDeclarations": seed_report["retainedDeclarations"],
        "seedDroppedDuplicates": seed_report["droppedDuplicateDeclarations"],
        "output": str(OUT.relative_to(ROOT)),
        "published": str(PUBLISHED.relative_to(ROOT)),
        "lines": len(text.splitlines()),
        "sha256": hashlib.sha256(text.encode()).hexdigest(),
        "byteIdenticalPublication": OUT.read_bytes() == PUBLISHED.read_bytes(),
    })
    REPORT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if not k.endswith("Declarations")}, indent=2))
    print(f"retained={len(report['retainedDeclarations'])} dropped={len(report['droppedDuplicateDeclarations'])}")


if __name__ == "__main__":
    main()
