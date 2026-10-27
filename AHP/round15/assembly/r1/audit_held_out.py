#!/usr/bin/env python3
"""Round-15 held-out right-star audit at q=1,R=34.

This is non-interval numerical evidence only, never a Lean premise or a proof
of the physical area seed, a normalized limit, P3, CofinalP3, or GoalNeg2.
"""
from pathlib import Path
import hashlib
import json
import mpmath as mp

H = Path(__file__).resolve().parent
ROOT = H.parents[3]
R14 = ROOT / "AHP/round14/assembly/r2"
mp.mp.dps = 190


def load(path):
    return json.loads(path.read_text())


def rel(a, b):
    a, b = mp.mpf(a), mp.mpf(b)
    return abs(a - b) / abs(b) if b else abs(a - b)


def main():
    p120 = load(H / "star_right_q1_R34_p120.json")
    p155 = load(H / "star_right_q1_R34_p155.json")
    r30 = load(R14 / "star_right_q1_R30_p120.json")
    r32 = load(R14 / "star_right_q1_R32_p120.json")
    j120 = list(map(mp.mpf, p120["first_physical_top_jet_sums"]))
    j155 = list(map(mp.mpf, p155["first_physical_top_jet_sums"]))
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
    rates = []
    for direction in range(3):
        old = abs(mp.mpf(r32["first_physical_top_jet_sums"][direction]) /
                  mp.mpf(r30["first_physical_top_jet_sums"][direction]))
        new = abs(j120[direction] /
                  mp.mpf(r32["first_physical_top_jet_sums"][direction]))
        rates.append({
            "direction": direction,
            "R30_to_R32_previous": str(old),
            "R32_to_R34_held_out": str(new),
            "relative_rate_change": str(abs(new - old) / old),
        })
        candidate_rates.append({
            "direction": direction,
            "candidate_rho_pow8": str(candidate),
            "R32_to_R34_held_out": str(new),
            "relative_difference": str(abs(new - candidate) / candidate),
        })
    checks = {
        "exits_zero": all((H / f"star_right_q1_R34_p{p}.exit").read_text().strip() == "0"
                          for p in (120, 155)),
        "unused_right_q1_R34": all(d["q"] == 1 and d["R"] == 34 and d["side"] == "right"
                                    for d in (p120, p155)),
        "tangential_positive_nonzero": all(j > 0 for j in j120[1:] + j155[1:]),
        "root_stability_below_1e100": root_rel < mp.power(10, -100),
        "jet_stability_below_1e100": all(x < mp.power(10, -100) for x in jet_rel),
        "residuals_below_1e40_of_jet": all(
            x["null_over_jet"] < mp.mpf("1e-40") and
            x["resolvent_over_jet"] < mp.mpf("1e-40") for x in residuals),
        "charged_scaling_below_1e100": all(
            x["charged_line_scaling_error"] < mp.power(10, -100) for x in residuals),
        "memory_below_2GiB": all(d["peak_rss_KiB"] < 2 * 1024**2 for d in (p120, p155)),
        "cell_ratios_exceed_one": all(x > 1 for x in ratios120 + ratios155),
        "held_out_rate_matches_previous_within_1e8": all(
            mp.mpf(x["relative_rate_change"]) < mp.mpf("1e-8") for x in rates),
        "candidate_rho_pow8_matches_heldout_within_1e8": all(
            mp.mpf(x["relative_difference"]) < mp.mpf("1e-8") for x in candidate_rates),
    }
    result = {
        "pass": all(checks.values()),
        "checks": checks,
        "original_right_q1_R34": {
            "root_relative_difference_120_155": str(root_rel),
            "top_jet_relative_differences_120_155": [str(x) for x in jet_rel],
            "max_abs_cell_over_abs_sum_120": [str(x) for x in ratios120],
            "max_abs_cell_over_abs_sum_155": [str(x) for x in ratios155],
            "residuals": [{k: str(v) if k != "dps" else v for k, v in x.items()}
                          for x in residuals],
            "high_precision_jets": p155["first_physical_top_jet_sums"],
            "areaSum_evidence_only": [str(2 * j) for j in j155],
            "successive_rate_audit": rates,
            "candidate_rho_pow8_audit": candidate_rates,
            "seconds": [p120["seconds"], p155["seconds"]],
            "peak_rss_KiB": [p120["peak_rss_KiB"], p155["peak_rss_KiB"]],
        },
        "artifacts": [
            {"path": str(p.relative_to(ROOT)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in [H / "right_star.py", H / "audit_held_out.py"]
            + [H / f"star_right_q1_R34_p{p}.{ext}"
               for p in (120, 155) for ext in ("json", "log", "exit")]
        ],
        "qualification": (
            "Finite non-interval numerical evidence only. q=1,R=34 was not used by the "
            "round-14 cancellation R=20,...,30 analysis or the assembly R=32 held-out audit. "
            "Stable positive tangential aggregates and a similar dominant rate do not prove "
            "an exact recurrence, RadiusDominantData, a matrix limit, a nonzero leading "
            "coefficient, AreaSeedRightStar, P3, CofinalP3, or GoalNeg2. Large cell/sum "
            "ratios continue to rule out a naive common-sign shortcut. Doubling a physical "
            "aggregate only applies the compiled aggregate=(1/2)*areaSum dictionary."
        ),
    }
    (H / "HELD_OUT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
