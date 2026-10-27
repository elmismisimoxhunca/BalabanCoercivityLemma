#!/usr/bin/env python3
"""Static and numerical-evidence audit for round-15 assembly R2."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parent
ROOT = H.parents[3]
LOCAL = H / "AreaGoal.lean"
SHARED = ROOT / "AHP/round15/shared/assembly/R2_AreaGoal.lean"
LOGS = [Path(str(LOCAL) + ".log"), Path(str(SHARED) + ".log")]
EXITS = [Path(str(LOCAL) + ".exit"), Path(str(SHARED) + ".exit")]
BUILD = H / "BUILD.json"
HELD = H / "HELD_OUT.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b"
)
MAIN = [
    "CofinalRadiusChargedLeadingData",
    "CofinalRadiusAreaSeed",
    "cofinalRadiusChargedLeadingData_of_chargedLeading",
    "cofinalRadiusAreaSeed_of_cofinalRadiusChargedLeadingData",
    "CofinalRadiusChargedLeadingCertificate",
    "cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading",
    "cofinalAreaSeed_of_cofinalRadiusChargedLeading",
    "goalNeg2_of_cofinalRadiusChargedLeading",
    "goalNeg2_of_cofinalAreaSeed",
]
BASE_MAIN = [
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
        "accepted_source_hash": sha(LOCAL) ==
            "a6d141eb46842741e72e9b8dd758fa1203c0dfa53c6b07a64ef6d86bf1ced5dc",
        "accepted_log_hash": sha(LOGS[1]) ==
            "8d9d20ba6b0647d5135310b4d2ea03cd2f9870999d4d40709c81f32b28ae142f",
        "retained_publication_record_reused": LOGS[0].read_bytes() == LOGS[1].read_bytes() and
            EXITS[0].read_bytes() == EXITS[1].read_bytes(),
        "both_lean_exits_zero": all(p.read_text().strip() == "0" for p in EXITS),
        "no_errors_or_sorryAx": all(
            "error:" not in p.read_text() and "sorryAx" not in p.read_text() for p in LOGS),
        "no_forbidden_proof_mechanism": FORBIDDEN.search(text) is None,
        "only_frozen_imports": [line for line in text.splitlines() if line.startswith("import ")] ==
            ["import DrEquiv", "import DrPath3"],
        "all_main_records_present_once_per_log": all(
            len(records(log, name)) == 1 for log in LOGS for name in MAIN + BASE_MAIN),
        "all_main_records_permitted": all(
            record <= ALLOWED for log in LOGS for name in MAIN + BASE_MAIN
            for record in records(log, name)),
        "main_statement_is_conditional":
            "theorem goalNeg2_of_cofinalRadiusChargedLeading\n    (h : CofinalRadiusChargedLeadingCertificate) : GoalNeg2" in text,
        "radius_cofinal_not_all_indices":
            "∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧" in text and
            "def CofinalRadiusChargedLeadingCertificate" in text,
        "old_certificate_weakened":
            "cofinalRadiusChargedLeadingCertificate_of_cofinalChargedLeading" in text,
        "failed_physical_dictionary_not_used":
            "Q1C10PhysicalDictionary" not in text and "DeepCollar" not in text,
        "held_out_numerics_pass": held["pass"] is True and
            (H / "HELD_OUT.exit").read_text().strip() == "0",
        "held_out_is_unused_q1_R42": held["original_right_q1_R42"] is not None and
            all((H / f"star_right_q1_R42_p{p}.exit").read_text().strip() == "0"
                for p in (120, 155)),
        "candidate_rate_retested": all(
            float(row["relative_difference"]) < 1e-8
            for row in held["original_right_q1_R42"]["candidate_rate_audit"]),
        "normalized_constant_retested": all(
            float(row["relative_difference"]) < 1e-8
            for row in held["original_right_q1_R42"]["normalized_constant_audit"]),
        "memory_below_2GiB": all(
            x < 2 * 1024**2
            for x in held["original_right_q1_R42"]["peak_rss_KiB"]),
        "partial_q2_probe_excluded":
            "no JSON and no .exit; not retried and not used" in held["excluded_partial_probe"]["status"],
    }
    result = {
        "pass": all(checks.values()),
        "checks": checks,
        "mainDeclarations": MAIN,
        "baseDeclarationsChecked": BASE_MAIN,
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
            "candidateRates": held["original_right_q1_R42"]["candidate_rate_audit"],
            "normalizedConstants": held["original_right_q1_R42"]["normalized_constant_audit"],
        },
        "boundary": (
            "All goal arrows are conditional on their displayed physical inputs. "
            "The new matrix certificate requires only cofinally many radii at each "
            "selected dyadic scale. No AreaSeedRightStar, CofinalUnitDominantAreaSeed, "
            "charged-leading certificate, P3, CofinalP3, or GoalNeg2 inhabitant is "
            "asserted. The unfinished dictionary R2 physical dictionary and the "
            "unassembled seed R2 vector certificate are not used. The retained "
            "publication log records an earlier successful compilation of the identical "
            "source; no independent recompilation is claimed."
        ),
    }
    (H / "AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
