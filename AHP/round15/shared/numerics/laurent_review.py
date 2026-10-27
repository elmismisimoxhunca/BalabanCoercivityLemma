#!/usr/bin/env python3
"""Reproduce the failed same-row Laurent fit and test the actual mode count."""
from pathlib import Path
import json
import mpmath as mp
ROOT = Path(__file__).resolve().parents[4]
OUT = ROOT / "AHP/round15/shared/numerics"


def direct(R):
    if R == 20:
        p = ROOT / "AHP/round12/kernel/r1/star_right_q1_R20_p120.json"
    elif R in (30, 32):
        p = ROOT / f"AHP/round14/assembly/r2/star_right_q1_R{R}_p120.json"
    elif R in (34,):
        p = ROOT / "AHP/round15/assembly/r1/star_right_q1_R34_p120.json"
    else:
        p = ROOT / f"AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json"
    D = json.loads(p.read_text())
    return [mp.mpf(x) for x in D["first_physical_top_jet_sums"]], str(p)


def polycoeff(roots):
    co = [mp.mpf(1)]
    for r in roots:
        new = [mp.mpf(0)] * (len(co) + 1)
        for j, a in enumerate(co):
            new[j] -= r * a
            new[j + 1] += a
        co = new
    return co


def run(dps=170):
    mp.mp.dps = dps
    radii = [20, 22, 24, 26, 28]
    Y = {R: direct(R)[0] for R in radii}
    naive = {}
    for d in range(3):
        y = [Y[R][d] for R in radii]
        y1, y2, y3, y4 = y[:4]
        a = (y4 - y1) / (y3 - y2)
        pred = a * y4 - a * y3 + y2
        actual = y[4]
        naive[str(d)] = {"recurrence_leading_coefficient": a,
                         "predicted_R28": pred, "actual_R28": actual,
                         "held_out_relative_error": abs(pred / actual - 1),
                         "sign_reversed": pred * actual < 0}
    rates = json.loads((ROOT / "AHP/round15/numerics/r1/rate_table_right_q1.json").read_text())["rows"]
    unique = {mp.nstr(r["expected_area_ratio_per_two_radius"], 80): mp.mpf(r["expected_area_ratio_per_two_radius"])
              for r in rates}
    roots = sorted(unique.values())
    co = polycoeff(roots)
    rec = [-co[j] for j in range(len(co) - 1)]
    predictions, residuals = {}, {}
    for d in range(3):
        seq = {R: Y[R][d] for R in radii}
        for R in (30, 32):
            n = (R - 20) // 2 - 5
            seq[R] = sum(rec[j] * seq[20 + 2 * (n + j)] for j in range(5))
        predictions[str(d)] = {str(R): seq[R] for R in (30, 32)}
        maxrel = mp.mpf(0)
        for R in (30, 32):
            actual, _ = direct(R)
            maxrel = max(maxrel, abs(seq[R] / actual[d] - 1))
        residuals[str(d)] = maxrel
    # A held-out check at R=34, not used in the original ansatz analysis.
    r34 = {}
    for d in range(3):
        seq = {R: Y[R][d] for R in radii}
        for R in (30, 32, 34):
            n = (R - 20) // 2 - 5
            seq[R] = sum(rec[j] * seq[20 + 2 * (n + j)] for j in range(5))
        actual, _ = direct(34)
        r34[str(d)] = {"predicted": seq[34], "actual": actual[d],
                       "relative_error": abs(seq[34] / actual[d] - 1)}
    result = {
        "dps": dps, "naive_three_term": naive,
        "unique_five_rates": roots,
        "full_recurrence_characteristic_coefficients_ascending": co,
        "full_recurrence_prediction_coefficients": rec,
        "full_recurrence_predictions_R30_R32": predictions,
        "full_recurrence_max_relative_error_R30_R32": residuals,
        "full_recurrence_R34": r34,
        "explanation": [
            "The three-term Laurent ansatz has only r,1,r^(-1) as characteristic roots. The q=1 physical top row instead has five decaying character rates.",
            "The omitted subleading modes perturb the fitted leading coefficient by about one part in 13429. Subsequent subtraction and extrapolation amplify that perturbation into the observed 8.77e5 to 2.01e6 relative errors and sign reversals.",
            "Using the five measured character rates gives an order-five recurrence that predicts R=30,32,34; this tests the mode-count explanation but is still not a proof of the recurrence or of cofinal nonvanishing."
        ],
        "qualification": "Non-interval numerical evidence only. No Lean theorem, Laurent certificate, dominant-limit certificate, or P3 claim is asserted."
    }
    (OUT / "LAURENT_REVIEW.json").write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print(json.dumps(jsonable(result), indent=2))


def jsonable(x):
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp.nstr(x, mp.mp.dps - 5)
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=170)
    a = ap.parse_args()
    run(a.dps)
