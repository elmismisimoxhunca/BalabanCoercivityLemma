#!/usr/bin/env python3
"""Audit the held-out right-star q=1,R=22 evidence; no proof claim."""
from pathlib import Path
import hashlib
import json
import mpmath as mp

H = Path(__file__).resolve().parent
mp.mp.dps = 190
low = json.loads((H / "star_right_q1_R22_p120.json").read_text())
high = json.loads((H / "star_right_q1_R22_p155.json").read_text())


def rel(a, b):
    a, b = mp.mpf(a), mp.mpf(b)
    return abs(a - b) / abs(b) if b else abs(a - b)


jets120 = list(map(mp.mpf, low["first_physical_top_jet_sums"]))
jets155 = list(map(mp.mpf, high["first_physical_top_jet_sums"]))
max120 = list(map(mp.mpf, low["max_abs_first_top_jet"]))
max155 = list(map(mp.mpf, high["max_abs_first_top_jet"]))
ratios120 = [m / abs(s) for m, s in zip(max120, jets120)]
ratios155 = [m / abs(s) for m, s in zip(max155, jets155)]
relative_jets = [rel(a, b) for a, b in zip(jets120, jets155)]
relative_root = rel(low["root"], high["root"])
residual_checks = []
for d, jets in ((low, jets120), (high, jets155)):
    detect = min(abs(jets[1]), abs(jets[2]))
    residual_checks.append({
        "dps": d["dps"],
        "null_residual_over_tangential_jet": str(mp.mpf(d["boundary_null_residual"]) / detect),
        "resolvent_residual_over_tangential_jet": str(mp.mpf(d["flat_resolvent_absolute_residual"]) / detect),
        "charged_line_scaling_max_relative_error": d["charged_line_scaling_max_relative_error"],
        "peak_rss_KiB": d["peak_rss_KiB"],
    })

checks = {
    "both_runs_exit_zero": all((H / f"star_right_q1_R22_p{p}.exit").read_text().strip() == "0" for p in (120, 155)),
    "held_out_right_q1_R22": all(d["q"] == 1 and d["R"] == 22 and d["side"] == "right" for d in (low, high)),
    "root_in_open_halfpi": all(0 < mp.mpf(d["root"]) < mp.pi / 2 for d in (low, high)),
    "next_charged_schur_value_positive": all(mp.mpf(d["charged_low"][1]) > 0 for d in (low, high)),
    "tangential_aggregates_nonzero": all(j != 0 for j in jets120[1:] + jets155[1:]),
    "tangential_aggregates_positive": all(j > 0 for j in jets120[1:] + jets155[1:]),
    "cell_ratios_exceed_one": all(r > 1 for r in ratios120 + ratios155),
    "root_relative_agreement_below_1e100": relative_root < mp.power(10, -100),
    "tangential_relative_agreement_below_1e100": all(r < mp.power(10, -100) for r in relative_jets[1:]),
    "residuals_small_against_jets": all(
        mp.mpf(x["null_residual_over_tangential_jet"]) < mp.mpf("1e-70") and
        mp.mpf(x["resolvent_residual_over_tangential_jet"]) < mp.mpf("1e-70")
        for x in residual_checks),
    "charged_line_scaling_below_1e100": all(
        mp.mpf(x["charged_line_scaling_max_relative_error"]) < mp.power(10, -100)
        for x in residual_checks),
    "memory_below_2GiB": all(x["peak_rss_KiB"] < 2 * 1024**2 for x in residual_checks),
}

paths = [H / "right_star.py", H / "audit_numerics.py"]
paths += [H / f"star_right_q1_R22_p{p}.{suffix}" for p in (120, 155) for suffix in ("json", "log", "exit")]
result = {
    "case": "held-out right star q=1,R=22; all 16 Fourier characters",
    "checks": checks,
    "pass": all(checks.values()),
    "root_relative_difference_120_155": str(relative_root),
    "top_jet_relative_differences_120_155": [str(x) for x in relative_jets],
    "max_abs_cell_over_abs_sum_120": [str(x) for x in ratios120],
    "max_abs_cell_over_abs_sum_155": [str(x) for x in ratios155],
    "residual_checks": residual_checks,
    "high_precision_values": {
        "root": high["root"],
        "next_charged_schur_value": high["charged_low"][1],
        "first_physical_top_jet_sums": high["first_physical_top_jet_sums"],
        "max_abs_first_top_jet": high["max_abs_first_top_jet"],
        "central_coordinate_abs": high["central_coordinate_abs"],
        "boundary_null_residual": high["boundary_null_residual"],
        "flat_resolvent_absolute_residual": high["flat_resolvent_absolute_residual"],
    },
    "area_dictionary_consequence_evidence_only": [
        str(2 * j) for j in jets155
    ],
    "artifacts": [
        {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
        for p in paths
    ],
    "qualification": (
        "Finite high-precision non-interval evidence only. The physical aggregate is computed; "
        "the doubled values merely apply the compiled aggregate=(1/2)*areaSum identity. "
        "No exact nonzero Lean value, no common-cell-sign certificate, no cofinal conclusion, "
        "and no P3 or GoalNeg2 proof is claimed. Ratios above one also show that a naive "
        "common-sign cell argument is unsupported on this held-out case."
    ),
}
(H / "NUMERICS.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
raise SystemExit(0 if result["pass"] else 1)
