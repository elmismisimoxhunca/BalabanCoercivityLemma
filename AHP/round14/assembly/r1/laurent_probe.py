#!/usr/bin/env python3
"""Held-out test of the natural same-row three-term Laurent ansatz.

The observable is the first physical top-jet aggregate in each direction.  A
three-term A*r^n+B+C*r^(-n) sequence has characteristic roots r,1,r^-1, hence
S:=r+r^-1 satisfies y_(n+3)=(S+1)y_(n+2)-(S+1)y_(n+1)+y_n.
Fit on R=20,22,24,26 and predict R=28.  This is numerical evidence only.
"""
from pathlib import Path
import hashlib
import json
import mpmath as mp

H = Path(__file__).resolve().parent
OLD = H.parents[2] / "round12/kernel/r1/star_right_q1_R20_p120.json"
mp.mp.dps = 170
D = {20: json.loads(OLD.read_text())}
for R in (22, 24, 26, 28):
    D[R] = json.loads((H / f"star_right_q1_R{R}_p120.json").read_text())

series = {}
for direction in range(3):
    y = [mp.mpf(D[R]["first_physical_top_jet_sums"][direction]) for R in (20, 22, 24, 26, 28)]
    windows = []
    for i in range(2):
        y1, y2, y3, y4 = y[i:i + 4]
        slope = (y4 - y1) / (y3 - y2) - 1  # r+r^-1
        r = (slope - mp.sqrt(slope * slope - 4)) / 2
        windows.append({
            "first_n": i + 1,
            "r_plus_inverse_plus_one": str(slope + 1),
            "smaller_root": str(r),
            "root_in_unit_interval": 0 < r < 1,
        })
    y1, y2, y3, y4 = y[:4]
    slope_plus_one = (y4 - y1) / (y3 - y2)
    predicted5 = slope_plus_one * y4 - slope_plus_one * y3 + y2
    relative_error = abs(predicted5 / y[4] - 1)
    series[str(direction)] = {
        "values_R20_R22_R24_R26_R28": [str(v) for v in y],
        "successive_absolute_ratios": [str(y[i] / y[i + 1]) for i in range(4)],
        "laurent_windows": windows,
        "predicted_R28_from_R20_through_R26": str(predicted5),
        "actual_R28": str(y[4]),
        "held_out_relative_error": str(relative_error),
        "held_out_prediction_within_factor_two": relative_error < 1,
    }

residuals = []
for R in (20, 22, 24, 26, 28):
    d = D[R]
    jets = list(map(mp.mpf, d["first_physical_top_jet_sums"]))
    detect = min(abs(jets[1]), abs(jets[2]))
    residuals.append({
        "R": R,
        "null_over_tangential": str(mp.mpf(d["boundary_null_residual"]) / detect),
        "resolvent_over_tangential": str(mp.mpf(d["flat_resolvent_absolute_residual"]) / detect),
    })

checks = {
    "all_new_runs_exit_zero": all((H / f"star_right_q1_R{R}_p120.exit").read_text().strip() == "0" for R in (22, 24, 26, 28)),
    "all_cases_right_q1": all(d["q"] == 1 and d["side"] == "right" for d in D.values()),
    "all_tangential_observations_nonzero": all(
        mp.mpf(D[R]["first_physical_top_jet_sums"][direction]) != 0
        for R in D for direction in (1, 2)),
    "naive_three_term_laurent_fails_held_out_R28": all(
        not series[str(direction)]["held_out_prediction_within_factor_two"]
        for direction in range(3)),
    "residuals_small_against_observations": all(
        mp.mpf(x["null_over_tangential"]) < mp.mpf("1e-55") and
        mp.mpf(x["resolvent_over_tangential"]) < mp.mpf("1e-55")
        for x in residuals),
}
paths = [H / "right_star.py", H / "laurent_probe.py", OLD]
paths += [H / f"star_right_q1_R{R}_p120.{suffix}" for R in (22, 24, 26, 28) for suffix in ("json", "log", "exit")]
result = {
    "case": "right star q=1, first physical top row, R=20,22,24,26,28 at 120 digits",
    "checks": checks,
    "pass": all(checks.values()),
    "series": series,
    "residuals": residuals,
    "artifacts": [
        {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
        for p in paths
    ],
    "qualification": (
        "Non-interval numerical evidence only. The exact three-term Laurent family "
        "A*r^n+B+C*r^(-n) has roots r,1,r^-1. The recurrence fitted on the first four "
        "radii fails badly at R=28 in all three directions. This rejects that natural "
        "same-row ansatz as a proof strategy; it does not reject nonzero detection, "
        "another top row, another generator, or the general conditional CofinalLaurentAreaSeed "
        "predicate. The continued nonzero samples do not prove P3 or cofinality."
    ),
}
(H / "LAURENT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
raise SystemExit(0 if result["pass"] else 1)
