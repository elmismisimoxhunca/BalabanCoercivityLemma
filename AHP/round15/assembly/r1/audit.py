#!/usr/bin/env python3
"""Static and numerical-evidence audit for the round-15 assembly R1 artifacts."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parent
ROOT = H.parents[3]
LOCAL = H / "AreaGoal.lean"
SHARED = ROOT / "AHP/round15/shared/assembly/R1_AreaGoal.lean"
LOGS = [Path(str(LOCAL) + ".log"), Path(str(SHARED) + ".log")]
EXITS = [Path(str(LOCAL) + ".exit"), Path(str(SHARED) + ".exit")]
BUILD = H / "BUILD.json"
HELD = H / "HELD_OUT.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b"
)
MAIN = [
    "goalNeg2_of_areaSeed",
    "goalNeg2_of_unitAreaSeed",
    "goalNeg2_of_cofinalAreaSeed",
    "goalNeg2_of_laurentAreaSeed",
    "goalNeg2_of_dominantAreaSeed",
    "goalNeg2_of_unitDominantAreaSeed",
    "goalNeg2_of_chargedLeading",
    "CofinalChargedLeadingCertificate",
    "cofinalUnitDominantAreaSeed_of_cofinalChargedLeading",
    "goalNeg2_of_cofinalChargedLeading",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def records(log, name):
    text = log.read_text()
    full = f"AdalyFormal.Round15.Assembly.{name}"
    found = []
    for match in re.finditer(
            re.escape("'" + full + "' depends on axioms:") + r"\s*\[(.*?)\]", text, re.S):
        found.append({part.strip() for part in match.group(1).split(",")})
    return found


def main():
    text = LOCAL.read_text()
    build = json.loads(BUILD.read_text())
    held = json.loads(HELD.read_text())
    checks = {
        "publication_byte_identical": LOCAL.read_bytes() == SHARED.read_bytes(),
        "build_hash_current": build["sha256"] == sha(LOCAL),
        "both_lean_exits_zero": all(p.read_text().strip() == "0" for p in EXITS),
        "no_errors_or_sorryAx": all(
            "error:" not in p.read_text() and "sorryAx" not in p.read_text() for p in LOGS),
        "no_forbidden_proof_mechanism": FORBIDDEN.search(text) is None,
        "only_frozen_imports": [line for line in text.splitlines() if line.startswith("import ")] ==
            ["import DrEquiv", "import DrPath3"],
        "all_main_records_present_once_per_log": all(
            len(records(log, name)) == 1 for log in LOGS for name in MAIN),
        "all_main_records_permitted": all(
            record <= ALLOWED for log in LOGS for name in MAIN for record in records(log, name)),
        "main_statement_is_conditional":
            "theorem goalNeg2_of_areaSeed\n    (h : AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar) : GoalNeg2" in text,
        "cofinal_charged_statement_present":
            "def CofinalChargedLeadingCertificate : Prop :=" in text and
            "∃ j : ℕ, j₀ ≤ j ∧" in text,
        "failed_dictionary_not_used": "AdalyFormal.Round15.Dictionary" not in text,
        "held_out_numerics_pass": held["pass"] is True and
            (H / "HELD_OUT.exit").read_text().strip() == "0",
        "held_out_is_q1_R34": held["original_right_q1_R34"] is not None and
            all((H / f"star_right_q1_R34_p{p}.exit").read_text().strip() == "0"
                for p in (120, 155)),
        "candidate_rate_retested": all(
            float(row["relative_difference"]) < 1e-8
            for row in held["original_right_q1_R34"]["candidate_rho_pow8_audit"]),
        "memory_below_2GiB": all(
            x < 2 * 1024**2
            for x in held["original_right_q1_R34"]["peak_rss_KiB"]),
    }
    result = {
        "pass": all(checks.values()),
        "checks": checks,
        "mainDeclarations": MAIN,
        "axiomRecords": {
            str(log.relative_to(ROOT)): {
                name: [sorted(record) for record in records(log, name)] for name in MAIN
            } for log in LOGS
        },
        "source": {
            "path": str(LOCAL.relative_to(ROOT)),
            "published": str(SHARED.relative_to(ROOT)),
            "lines": len(text.splitlines()),
            "sha256": sha(LOCAL),
        },
        "heldOutEvidence": {
            "path": str(HELD.relative_to(ROOT)),
            "qualification": held["qualification"],
            "candidateRates": held["original_right_q1_R34"]["candidate_rho_pow8_audit"],
        },
        "boundary": (
            "All goal arrows are conditional on their displayed physical inputs. "
            "No AreaSeedRightStar, CofinalUnitDominantAreaSeed, charged-leading "
            "certificate, P3, CofinalP3, or GoalNeg2 inhabitant is asserted. "
            "The failed round-15 dictionary R1 prototype is not imported or used."
        ),
    }
    (H / "AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
