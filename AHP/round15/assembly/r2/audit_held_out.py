#!/usr/bin/env python3
"""Independent held-out original-right-star audit at q=1,R=42.

R=42 lies beyond every R=18,...,40 direct sweep in numerics R1.  All values
are finite non-interval numerical evidence, never Lean premises or proofs.
"""
from pathlib import Path
import hashlib
import json
import mpmath as mp

H = Path(__file__).resolve().parent
ROOT = H.parents[3]
NUM = ROOT / "AHP/round15/shared/numerics/dominant_right_q1.json"
mp.mp.dps = 190


def load(path):
    return json.loads(path.read_text())


def rel(a, b):
    a, b = mp.mpf(a), mp.mpf(b)
    return abs(a - b) / abs(b) if b else abs(a - b)


def main():
    p120 = load(H / "star_right_q1_R42_p120.json")
    p155 = load(H / "star_right_q1_R42_p155.json")
    anchor = load(H / "star_right_q1_R36_p120.json")
    direct = load(NUM)
    assert max(direct["radii"]) == 40 and 42 not in direct["radii"]
    direct40 = next(row for row in direct["table"] if row["R"] == 40)
    referenceK = mp.mpf(direct40["normalized_leading_constant"])
    j120 = list(map(mp.mpf, p120["first_physical_top_jet_sums"]))
    j155 = list(map(mp.mpf, p155["first_physical_top_jet_sums"]))
    janchor = list(map(mp.mpf, anchor["first_physical_top_jet_sums"]))
    root_rel = rel(p120["root"], p155["root"])
    jet_rel = [rel(a, b) for a, b in zip(j120, j155)]
    ratios120 = [m / abs(s) for m, s in zip(
        map(mp.mpf, p120["max_abs_first_top_jet"]), j120)]
    ratios155 = [m / abs(s) for m, s in zip(
        map(mp.mpf, p155["max_abs_first_top_jet"]), j155)]
    residuals = []
    for data, jets in ((p120, j120), (p155, j155)):
        detect = min(abs(jets[1]), abs(jets[2]))
        residuals.append({
            "dps": data["dps"],
            "null_over_jet": mp.mpf(data["boundary_null_residual"]) / detect,
            "resolvent_over_jet": mp.mpf(data["flat_resolvent_absolute_residual"]) / detect,
            "charged_line_scaling_error": mp.mpf(data["charged_line_scaling_max_relative_error"]),
        })
    rho = (5 - mp.sqrt(2) - mp.sqrt(23 - 10 * mp.sqrt(2))) / 2
    candidate = rho ** 8
    candidate_rates = []
    for direction in range(3):
        # R=36 to R=42 is three radius increments of two.  R=42 itself is
        # outside the direct R=18,...,40 sweep; R=36 is only the rate anchor.
        rate = abs(j120[direction] / janchor[direction]) ** (mp.mpf(1) / 3)
        candidate_rates.append({
            "direction": direction,
            "candidate_rho_pow8": str(candidate),
            "R36_to_R42_geometric_mean_rate": str(rate),
            "relative_difference": str(abs(rate - candidate) / candidate),
        })
    normalized = []
    for data, jets in ((p120, j120), (p155, j155)):
        area = 2 * jets[1]
        K = area / rho ** (4 * 42)
        normalized.append({
            "dps": data["dps"],
            "areaSum_evidence_only": str(area),
            "normalized_full_area_constant": str(K),
            "direct_R40_constant": str(referenceK),
            "relative_difference": str(abs(K - referenceK) / abs(referenceK)),
        })
    checks = {
        "exits_zero": all((H / f"star_right_q1_R42_p{p}.exit").read_text().strip() == "0"
                          for p in (120, 155)),
        "R42_beyond_author_direct_sweep": max(direct["radii"]) < 42 and
            all(d["q"] == 1 and d["R"] == 42 and d["side"] == "right"
                for d in (p120, p155)),
        "tangential_positive_nonzero": all(j > 0 for j in j120[1:] + j155[1:]),
        "root_stability_below_1e100": root_rel < mp.power(10, -100),
        "jet_stability_below_1e100": all(x < mp.power(10, -100) for x in jet_rel),
        "residuals_below_1e25_of_jet": all(
            x["null_over_jet"] < mp.mpf("1e-25") and
            x["resolvent_over_jet"] < mp.mpf("1e-25") for x in residuals),
        "charged_scaling_below_1e100": all(
            x["charged_line_scaling_error"] < mp.power(10, -100) for x in residuals),
        "memory_below_2GiB": all(d["peak_rss_KiB"] < 2 * 1024**2 for d in (p120, p155)),
        "cell_ratios_exceed_one": all(x > 1 for x in ratios120 + ratios155),
        "candidate_rate_matches_heldout_within_1e8": all(
            mp.mpf(x["relative_difference"]) < mp.mpf("1e-8") for x in candidate_rates),
        "normalized_constant_matches_direct_R40_within_1e8": all(
            mp.mpf(x["relative_difference"]) < mp.mpf("1e-8") for x in normalized),
        "anchor_exits_zero": (H / "star_right_q1_R36_p120.exit").read_text().strip() == "0" and
            (H / "star_right_q1_R36_p155.exit").read_text().strip() == "0",
    }
    result = {
        "pass": all(checks.values()),
        "checks": checks,
        "original_right_q1_R42": {
            "root_relative_difference_120_155": str(root_rel),
            "top_jet_relative_differences_120_155": [str(x) for x in jet_rel],
            "max_abs_cell_over_abs_sum_120": [str(x) for x in ratios120],
            "max_abs_cell_over_abs_sum_155": [str(x) for x in ratios155],
            "residuals": [{k: str(v) if k != "dps" else v for k, v in x.items()}
                          for x in residuals],
            "high_precision_jets": p155["first_physical_top_jet_sums"],
            "candidate_rate_audit": candidate_rates,
            "normalized_constant_audit": normalized,
            "seconds": [p120["seconds"], p155["seconds"]],
            "peak_rss_KiB": [p120["peak_rss_KiB"], p155["peak_rss_KiB"]],
        },
        "excluded_partial_probe": {
            "case": "q=2,R=42,dps=70",
            "status": "shell timeout after 31 of 64 sectors; no JSON and no .exit; not retried and not used",
        },
        "artifacts": [
            {"path": str(p.relative_to(ROOT)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in [H / "right_star.py", H / "audit_held_out.py"]
            + [H / f"star_right_q1_R42_p{p}.{ext}"
               for p in (120, 155) for ext in ("json", "log", "exit")]
            + [H / f"star_right_q1_R36_p{p}.{ext}"
               for p in (120, 155) for ext in ("json", "log", "exit")]
        ],
        "qualification": (
            "Finite non-interval numerical evidence only. The primary q=1,R=42 case is "
            "outside every R=18,...,40 direct sweep used by numerics R1. Stable positive "
            "tangential aggregates, the candidate rho^8 rate, and a stable normalized "
            "constant do not prove an exact recurrence, RadiusDominantData, a matrix limit, "
            "a nonzero leading coefficient, AreaSeedRightStar, P3, CofinalP3, or GoalNeg2. "
            "Large cell/sum ratios rule out a naive common-sign shortcut. Doubling a "
            "physical aggregate only applies the compiled aggregate=(1/2)*areaSum dictionary."
        ),
    }
    (H / "HELD_OUT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
