#!/usr/bin/env python3
"""Summarize exact algebraic rates and direct normalized leading constants."""
from pathlib import Path
import json
import mpmath as mp
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"


def independent_area(q, R):
    if q == 1:
        if R == 20:
            p = ROOT / "AHP/round12/kernel/r1/star_right_q1_R20_p120.json"
        elif R in (22, 24, 26, 28):
            p = ROOT / f"AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json"
        elif R in (30, 32):
            p = ROOT / f"AHP/round14/assembly/r2/star_right_q1_R{R}_p120.json"
        elif R == 34:
            p = ROOT / "AHP/round15/assembly/r1/star_right_q1_R34_p120.json"
        else:
            return None
        D = json.loads(p.read_text())
        return 2 * mp.mpf(D["first_physical_top_jet_sums"][1]), str(p)
    if q == 2 and R == 20:
        p = ROOT / "AHP/round12/kernel/r2/star_right_q2_R20_p155.json"
        D = json.loads(p.read_text())
        return 2 * mp.mpf(D["first_physical_top_jet_sums"][1]), str(p)
    if q == 4 and R in (18, 20):
        p = ROOT / f"AHP/round14/pathchoice/r2/long_q{q}_R{R}_L3_L3_q{q}_R{R}.json"
        D = json.loads(p.read_text())
        for v in D["variants"]:
            if v["name"] == "original":
                return 2 * mp.mpf(v["first_physical_top_jet_sums"][1][0]), str(p)
    return None


def real_string(s):
    z = s.strip().strip("()").split()
    return mp.mpf(z[0])


def run():
    mp.mp.dps = 100
    rows = []
    for q in (1, 2, 4):
        path = BASE / f"dominant_right_q{q}.json"
        characteristic = BASE / f"characteristic_q{q}_c0_1.json"
        if not path.exists() or not characteristic.exists():
            continue
        D = json.loads(path.read_text())
        C = json.loads(characteristic.read_text())
        y = real_string(C["dominant_y"]["numeric"])
        disc = real_string(C["dominant_discriminant"]["numeric"])
        rho = (y - mp.sqrt(disc)) / 2
        rate = rho ** (8 * q)
        direct_rate = mp.mpf(D["dominant_ratio_per_two_radius"])
        normalized = [mp.mpf(r["normalized_leading_constant"]) for r in D["table"]]
        checks = []
        for row in D["table"]:
            R = row["R"]
            old = independent_area(q, R)
            if old is None:
                continue
            value, source = old
            checks.append({"R": R, "source": source,
                           "independent_areaSum": value,
                           "dominant_areaSum": mp.mpf(row["areaSum_dominant_characters"]),
                           "dominant_minus_independent_over_independent": mp.mpf(row["areaSum_dominant_characters"]) / value - 1,
                           "independent_normalized_constant": value / rate ** (mp.mpf(R) / 2)})
        rows.append({
            "independent_checks": checks,
            "q": q, "dominant_y": y, "discriminant": disc, "rho_small": rho,
            "rate_per_two_radius": rate, "direct_rate_from_sweep": direct_rate,
            "rate_relative_difference": direct_rate / rate - 1,
            "characteristic_factor_residual_terms": sum(bool(z["terms"]) for z in C["factor_residual_highest_first"]),
            "normalized_constant_R18": normalized[0], "normalized_constant_R40": normalized[-1],
            "normalized_min": min(normalized), "normalized_max": max(normalized),
            "normalized_R18_to_R40_relative_change": normalized[-1] / normalized[0] - 1,
            "table": D["table"],
            "drive": D["drive"], "root": D["root"], "dps": D["dps"],
        })
    result = {
        "rows": rows,
        "normalization": "K_R=area_R/rate^(R/2), where rate is the exact candidate ratio per R->R+2 and area_R uses the four slowest characters only",
        "qualification": "Exact algebraic characteristic-factor arithmetic plus direct non-interval high-precision areas. No interval proof, seed projection proof, full-carrier normalization, or Lean/cofinal certificate."
    }
    (BASE / "LEADING_SUMMARY.json").write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print(json.dumps(jsonable({k: v for k, v in result.items() if k != "rows"}), indent=2))
    for row in rows:
        print("Q", row["q"], "rate", row["rate_per_two_radius"],
              "K18", row["normalized_constant_R18"], "K40", row["normalized_constant_R40"],
              "factor residual", row["characteristic_factor_residual_terms"])


def jsonable(x):
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp.nstr(x, mp.mp.dps - 5)
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


if __name__ == "__main__":
    run()
