#!/usr/bin/env python3
"""Independent held-out tests of the R2 dominant-area and L3-path claims.

All outputs are numerical evidence only.  No result here is a Lean certificate.
"""
from pathlib import Path
import hashlib
import json
import mpmath as mp

H = Path(__file__).resolve().parent
R1 = H.parents[0] / "r1"
mp.mp.dps = 190


def load(name):
    return json.loads((H / name).read_text())


def rel(a, b):
    a, b = mp.mpf(a), mp.mpf(b)
    return abs(a - b) / abs(b) if b else abs(a - b)


def exits(names):
    return all((H / name).read_text().strip() == "0" for name in names)


# Original right star R=32: not used by cancellation R2's R=20,...,30 analysis.
o120 = load("star_right_q1_R32_p120.json")
o155 = load("star_right_q1_R32_p155.json")
oj120 = list(map(mp.mpf, o120["first_physical_top_jet_sums"]))
oj155 = list(map(mp.mpf, o155["first_physical_top_jet_sums"]))
om120 = list(map(mp.mpf, o120["max_abs_first_top_jet"]))
om155 = list(map(mp.mpf, o155["max_abs_first_top_jet"]))
oratio120 = [m / abs(s) for m, s in zip(om120, oj120)]
oratio155 = [m / abs(s) for m, s in zip(om155, oj155)]
oj_rel = [rel(a, b) for a, b in zip(oj120, oj155)]
oroot_rel = rel(o120["root"], o155["root"])
oresidual = []
for d, jets in ((o120, oj120), (o155, oj155)):
    detect = min(abs(jets[1]), abs(jets[2]))
    oresidual.append({
        "dps": d["dps"],
        "null_over_jet": str(mp.mpf(d["boundary_null_residual"]) / detect),
        "resolvent_over_jet": str(mp.mpf(d["flat_resolvent_absolute_residual"]) / detect),
        "charged_line_scaling_error": d["charged_line_scaling_max_relative_error"],
        "peak_rss_KiB": d["peak_rss_KiB"],
    })

# Compare successive R=28->30 and held-out R=30->32 rates at 120 digits.
r28 = json.loads((R1 / "star_right_q1_R28_p120.json").read_text())["first_physical_top_jet_sums"]
r30 = load("star_right_q1_R30_p120.json")["first_physical_top_jet_sums"]
rates = []
for direction in range(3):
    old = abs(mp.mpf(r30[direction]) / mp.mpf(r28[direction]))
    new = abs(mp.mpf(oj120[direction]) / mp.mpf(r30[direction]))
    rates.append({
        "direction": direction,
        "R28_to_R30": str(old),
        "R30_to_R32_held_out": str(new),
        "relative_rate_change": str(abs(new - old) / old),
    })

# L3 path candidate at q=2,R=30, not used by path-choice R2.
t120 = load("tail_q2_R30_c2_m0_25_c3_m2_25_p120.json")
t155 = load("tail_q2_R30_c2_m0_25_c3_m2_25_p155.json")
tdouble = load("long_q2_R30_L3_L3_q2_R30.json")
tvariant = next(v for v in tdouble["variants"] if v["name"] == "candidate")
tr120, tr155 = t120["right_row"], t155["right_row"]
tsum120, tsum155 = mp.mpf(tr120["sum"]), mp.mpf(tr155["sum"])
trat120, trat155 = mp.mpf(tr120["max_over_abs_sum"]), mp.mpf(tr155["max_over_abs_sum"])
tl1120, tl1155 = mp.mpf(tr120["abs_sum_over_l1"]), mp.mpf(tr155["abs_sum_over_l1"])
t_sum_rel = rel(tsum120, tsum155)
t_ratio_rel = rel(trat120, trat155)
t_l1_rel = rel(tl1120, tl1155)
t_res155 = mp.mpf(t155["flat_resolvent_absolute_residual"]) / abs(tsum155)
t_double_sum_rel = rel(tvariant["first_physical_top_jet_sums"][1][0], tsum155)
t_double_ratio_rel = rel(tvariant["max_over_abs_sum"][1], trat155)
t_root_diff = abs(mp.mpf(tvariant["root"]) - mp.mpf(t155["root_double"]))
t_checks = {
    "tail_exits_zero": exits(["screen_tail_q2_R30.exit", "verify_tail_q2_R30_p120.exit", "verify_tail_q2_R30_p155.exit"]),
    "tail_is_unused_q2_R30_candidate": t155["q"] == 2 and t155["R"] == 30 and
        t155["second_segment_coefficient"] == -0.25 and t155["third_segment_coefficient"] == -2.25,
    "tail_right_row_nonzero": tsum120 != 0 and tsum155 != 0,
    "tail_right_row_positive": tsum120 > 0 and tsum155 > 0,
    "tail_ratio_below_one": trat120 < 1 and trat155 < 1,
    "tail_stability_below_1e100": max(t_sum_rel, t_ratio_rel, t_l1_rel) < mp.power(10, -100),
    "tail_residual_below_1e30_of_sum": t_res155 < mp.mpf("1e-30"),
    "tail_double_high_agreement_below_1e8": max(t_double_sum_rel, t_double_ratio_rel) < mp.mpf("1e-8"),
    "tail_root_matches_double": t_root_diff == 0,
    "tail_sampled_spectral_diagnostics_positive": all(x > 0 for x in t155["central_zero_schur_min_double"]) and
        t155["charged_low_double"][1] > 0 and t155["neutral_min_double"] > 0,
    "tail_memory_below_2GiB": all(d["peak_rss_KiB"] < 2 * 1024**2 for d in (t120, t155)),
}

checks = {
    "original_R32_exits_zero": exits(["star_right_q1_R32_p120.exit", "star_right_q1_R32_p155.exit"]),
    "original_R32_is_right_q1": o120["q"] == o155["q"] == 1 and o120["R"] == o155["R"] == 32 and
        o120["side"] == o155["side"] == "right",
    "original_R32_tangential_nonzero_positive": all(j > 0 for j in oj120[1:] + oj155[1:]),
    "original_R32_cell_ratios_exceed_one": all(r > 1 for r in oratio120 + oratio155),
    "original_R32_root_stability_below_1e100": oroot_rel < mp.power(10, -100),
    "original_R32_jet_stability_below_1e100": all(r < mp.power(10, -100) for r in oj_rel[1:]),
    "original_R32_residuals_below_1e50_of_jet": all(
        mp.mpf(x["null_over_jet"]) < mp.mpf("1e-50") and
        mp.mpf(x["resolvent_over_jet"]) < mp.mpf("1e-50") for x in oresidual),
    "original_R32_scaling_below_1e100": all(
        mp.mpf(x["charged_line_scaling_error"]) < mp.power(10, -100) for x in oresidual),
    "original_R32_memory_below_2GiB": all(x["peak_rss_KiB"] < 2 * 1024**2 for x in oresidual),
    "held_out_rate_matches_previous_within_1e8": all(
        mp.mpf(x["relative_rate_change"]) < mp.mpf("1e-8") for x in rates),
    **t_checks,
}

paths = [H / x for x in [
    "right_star.py", "screen_tail_instance.py", "verify_tail_mp.py", "audit_held_out.py",
    "star_right_q1_R32_p120.json", "star_right_q1_R32_p120.log", "star_right_q1_R32_p120.exit",
    "star_right_q1_R32_p155.json", "star_right_q1_R32_p155.log", "star_right_q1_R32_p155.exit",
    "long_q2_R30_L3_L3_q2_R30.json", "screen_tail_q2_R30.log", "screen_tail_q2_R30.exit",
    "tail_q2_R30_c2_m0_25_c3_m2_25_p120.json", "verify_tail_q2_R30_p120.log", "verify_tail_q2_R30_p120.exit",
    "tail_q2_R30_c2_m0_25_c3_m2_25_p155.json", "verify_tail_q2_R30_p155.log", "verify_tail_q2_R30_p155.exit",
]]
result = {
    "pass": all(checks.values()),
    "checks": checks,
    "original_right_q1_R32": {
        "root_relative_difference_120_155": str(oroot_rel),
        "top_jet_relative_differences_120_155": [str(x) for x in oj_rel],
        "max_abs_cell_over_abs_sum_120": [str(x) for x in oratio120],
        "max_abs_cell_over_abs_sum_155": [str(x) for x in oratio155],
        "residuals": oresidual,
        "high_precision_jets": o155["first_physical_top_jet_sums"],
        "areaSum_evidence_only": [str(2 * j) for j in oj155],
        "successive_rate_audit": rates,
    },
    "L3_candidate_q2_R30": {
        "root_double": t155["root_double"],
        "right_row_j": t155["right_row_j"],
        "right_row_sum": tr155["sum"],
        "areaSum_evidence_only": str(2 * tsum155),
        "max_over_abs_sum_120_155": [tr120["max_over_abs_sum"], tr155["max_over_abs_sum"]],
        "abs_sum_over_l1_120_155": [tr120["abs_sum_over_l1"], tr155["abs_sum_over_l1"]],
        "negative_positive_cells": [tr155["negative_count"], tr155["positive_count"]],
        "common_weak_sign_rows": t155["common_weak_sign_rows"],
        "best_ratio_row_j": t155["best_ratio_row_j"],
        "best_l1_row_j": t155["best_l1_row_j"],
        "sum_relative_difference_120_155": str(t_sum_rel),
        "ratio_relative_difference_120_155": str(t_ratio_rel),
        "l1_relative_difference_120_155": str(t_l1_rel),
        "residual_over_sum_155": str(t_res155),
        "double_high_sum_relative_difference": str(t_double_sum_rel),
        "double_high_ratio_relative_difference": str(t_double_ratio_rel),
        "central_zero_schur_min_double": t155["central_zero_schur_min_double"],
        "charged_low_double": t155["charged_low_double"],
        "peak_rss_KiB": [t120["peak_rss_KiB"], t155["peak_rss_KiB"]],
    },
    "artifacts": [
        {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
        for p in paths
    ],
    "qualification": (
        "Finite non-interval numerical evidence only. R=32 was not used in cancellation R2's "
        "dominant-rate analysis; q=2,R=30 was not used in path-choice R2's L3 analysis. "
        "The R=32 rate remains close to the previous rate and the L3 right-row sum remains "
        "nonzero with max|cell|/|sum| below one. These support the authors' numerical leads "
        "but do not supply an exact rate, a matrix limit, a nonzero leading coefficient, "
        "P1/P2/KernelLine, an area seed, or P3. The L3 cells still have mixed signs and no "
        "computed row has a common weak sign. Doubling a physical aggregate merely applies "
        "the compiled aggregate=(1/2)*areaSum dictionary."
    ),
}
(H / "HELD_OUT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
raise SystemExit(0 if result["pass"] else 1)
