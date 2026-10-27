#!/usr/bin/env python3
"""Recompute R=18..40 normalized constants from retained direct flat solves.

No new physical solve is performed.  The exact characteristic rate is evaluated
at high working precision; input areas retain their original finite precision.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"
import json
import mpmath as mp
import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def jsonable(x):
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp.nstr(x, mp.mp.dps - 5)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


def run(dps=170):
    mp.mp.dps = dps
    expected_radii = list(range(18, 42, 2))
    rows = []
    for q in (1, 2, 4):
        D = json.loads((BASE / f"dominant_right_q{q}.json").read_text())
        N = 4 * q
        s = 5 - 2 * mp.cos(mp.pi / N)
        rho = (s - mp.sqrt(s * s - 4)) / 2
        rate = rho ** (8 * q)
        table = []
        for old in D["table"]:
            R = old["R"]
            area = mp.mpf(old["areaSum_dominant_characters"])
            K = area / rate ** (mp.mpf(R) / 2)
            stored = mp.mpf(old["normalized_leading_constant"])
            table.append({"R": R, "areaSum_four_dominant_characters": area,
                          "normalized_leading_constant": K,
                          "stored_normalized_minus_recomputed": stored - K,
                          "per_character": old["per_character"]})
        assert [r["R"] for r in table] == expected_radii
        K = [r["normalized_leading_constant"] for r in table]
        residuals = [mp.mpf(rec["flat_resolvent_absolute_residual"]) for rec in D["records"]]
        nulls = [mp.mpf(rec["augmented_null_max"]) for rec in D["records"]
                 if rec.get("augmented_null_max") is not None]
        ratio_errors = [abs(mp.mpf(c["ratio_relative_error"])) for row in table
                        for c in row["per_character"] if c["ratio_relative_error"] is not None]
        rows.append({
            "q": q, "root": D["root"], "drive": D["drive"], "source_dps": D["dps"],
            "dominant_characters": D["dominant_characters"],
            "s": s, "rho": rho, "rate_per_two_radius": rate,
            "table": table, "K_R18": K[0], "K_R40": K[-1],
            "K_R40_over_K_R18_minus_one": K[-1] / K[0] - 1,
            "K_min": min(K), "K_max": max(K),
            "max_flat_resolvent_absolute_residual": max(residuals),
            "max_augmented_null_available": max(nulls),
            "augmented_null_record_count": len(nulls),
            "max_stored_successive_rate_relative_error": max(ratio_errors),
            "record_count": len(D["records"]),
        })
    laurent = json.loads((BASE / "R2_LAURENT_REVIEW.json").read_text())
    result = {
        "working_dps": dps, "radii": expected_radii, "rows": rows,
        "q1_full_area_crosscheck": laurent["leading_constant_comparison"],
        "normalization": "At each R, area is the sum of the four slowest characters divided by (4q)^2; K_R=area/rate^(R/2). Subleading characters are not included in this dominant-channel area.",
        "precision_boundary": "Rates and normalization are recomputed at 170 working digits from exact algebraic formulas. Areas are reused from the R1 direct non-interval solves (source_dps=70, with fewer reliable trailing digits); no new solve or 170-digit accuracy claim is made.",
        "qualification": "High-precision numerical evidence only. No interval bound, exact amplitude closed form, common finite seed, normalized matrix limit, full-carrier normalization, physical area seed, or GoalNeg2 proof.",
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    (BASE / "R2_LEADING_STABILITY.json").write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print(json.dumps(jsonable({"working_dps": dps,
                               "rows": [{k: v for k, v in row.items() if k not in ("table", "dominant_characters")}
                                        for row in rows],
                               "q1_full_area_crosscheck": result["q1_full_area_crosscheck"],
                               "peak_rss_KiB": result["peak_rss_KiB"]}), indent=2))


if __name__ == "__main__":
    run()
