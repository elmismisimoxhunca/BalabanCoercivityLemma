#!/usr/bin/env python3
"""R2 held-out Laurent review using the exact all-character mode dictionary.

The naive four-point fit is reproduced.  A five-slowest-channel model is then
fitted on R=20,...,28 and tested on R=30,32,34.  The latter is still only an
accurate numerical model: the exact companion has further reciprocal branches,
and no exact Laurent/cofinal certificate is inferred.
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


def direct(R):
    if R == 20:
        p = ROOT / "AHP/round12/kernel/r1/star_right_q1_R20_p120.json"
    elif R in (30, 32):
        p = ROOT / f"AHP/round14/assembly/r2/star_right_q1_R{R}_p120.json"
    elif R == 34:
        p = ROOT / "AHP/round15/assembly/r1/star_right_q1_R34_p120.json"
    else:
        p = ROOT / f"AHP/round14/assembly/r1/star_right_q1_R{R}_p120.json"
    D = json.loads(p.read_text())
    return [mp.mpf(x) for x in D["first_physical_top_jet_sums"]], str(p.relative_to(ROOT))


def polycoeff(roots):
    co = [mp.mpf(1)]
    for r in roots:
        new = [mp.mpf(0)] * (len(co) + 1)
        for j, a in enumerate(co):
            new[j] -= r * a
            new[j + 1] += a
        co = new
    return co


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
    factors = json.loads((BASE / "R2_EXACT_FACTORS_q1.json").read_text())
    channels = {}
    for rec in factors["records"]:
        iy, iz = rec["character"]
        if (iy, iz) == (0, 0):
            s = mp.mpf(7)
            suppressed = True
        else:
            # q=1: X,Z are the integers 2 or 4.  Read their exact rational
            # constant terms rather than using a rounded numeric field.
            def rational_constant(z):
                terms = z["terms"]
                assert all(int(k) == 0 for k, _ in terms)
                return sum(mp.mpf(v) for _, v in terms)
            X, Z = rational_constant(rec["X"]), rational_constant(rec["Z"])
            s = 7 - mp.sqrt(X) - mp.sqrt(Z)
            suppressed = False
        key = mp.nstr(s, 100)
        rho = (s - mp.sqrt(s * s - 4)) / 2
        rate = rho ** 8
        if key not in channels:
            channels[key] = {"s": s, "rho": rho, "rate": rate,
                             "characters": [], "uniform_y3_channel_suppressed": suppressed}
        channels[key]["characters"].append([iy, iz])
    ordered = sorted(channels.values(), key=lambda c: c["rate"], reverse=True)
    assert len(ordered) == 5
    roots = [c["rate"] for c in ordered]
    radii = [20, 22, 24, 26, 28]
    data, sources = {}, {}
    for R in [20, 22, 24, 26, 28, 30, 32, 34]:
        data[R], sources[str(R)] = direct(R)
    naive = {}
    leading = roots[0]
    ideal_a = 1 + leading + 1 / leading
    for d in range(3):
        y = [data[R][d] for R in radii]
        y1, y2, y3, y4 = y[:4]
        a = (y4 - y1) / (y3 - y2)
        pred = a * y4 - a * y3 + y2
        actual = y[4]
        naive[str(d)] = {
            "fitted_recurrence_leading_coefficient": a,
            "ideal_single_rate_laurent_coefficient": ideal_a,
            "fitted_minus_ideal": a - ideal_a,
            "fitted_over_ideal_minus_one": a / ideal_a - 1,
            "predicted_R28": pred, "actual_R28": actual,
            "held_out_relative_error": abs(pred / actual - 1),
            "sign_reversed": pred * actual < 0,
        }
    co = polycoeff(roots)
    recurrence_coefficients = [-co[j] for j in range(len(co) - 1)]
    recurrence_predictions = {}
    for d in range(3):
        seq = {R: data[R][d] for R in radii}
        rows = {}
        for R in (30, 32, 34):
            n = (R - 20) // 2 - 5
            seq[R] = sum(recurrence_coefficients[j] * seq[20 + 2 * (n + j)] for j in range(5))
            rows[str(R)] = {"predicted": seq[R], "actual": data[R][d],
                            "relative_error": abs(seq[R] / data[R][d] - 1)}
        recurrence_predictions[str(d)] = rows
    # An equivalent basis-amplitude computation gives the full-area leading
    # constant directly, rather than only its four-dominant-character sum.
    M = mp.matrix([[r ** n for r in roots] for n in range(5)])
    amplitude_fits = {}
    for d in range(3):
        b = mp.matrix([data[20 + 2 * n][d] for n in range(5)])
        amplitudes = list(mp.lu_solve(M, b))
        modes = []
        for channel, r, a in zip(ordered, roots, amplitudes):
            B = a / r ** 10  # R=20 corresponds to exponent R/2=10.
            modes.append({"s": channel["s"], "rate": r,
                          "characters": channel["characters"],
                          "R20_basis_amplitude": a,
                          "jet_coefficient_of_rate_power_R_over_2": B,
                          "areaSum_coefficient": 2 * B})
        amplitude_fits[str(d)] = {"modes": modes,
                                  "leading_full_areaSum_constant": 2 * modes[0]["jet_coefficient_of_rate_power_R_over_2"]}
    leading_summary = json.loads((BASE / "LEADING_SUMMARY.json").read_text())
    q1 = next(r for r in leading_summary["rows"] if r["q"] == 1)
    direct_dominant_K = mp.mpf(q1["normalized_constant_R40"])
    full_fit_K = amplitude_fits["1"]["leading_full_areaSum_constant"]
    comparison = {
        "full_five_channel_fit_direction1_areaSum": full_fit_K,
        "direct_four_dominant_character_areaSum_R40_normalized": direct_dominant_K,
        "absolute_difference": full_fit_K - direct_dominant_K,
        "relative_difference": full_fit_K / direct_dominant_K - 1,
        "interpretation": "Independent numerical agreement for the common leading constant. This is not an exact algebraic identity or an interval bound."
    }
    result = {
        "dps": dps, "sources": sources,
        "mode_dictionary_source": "AHP/round15/shared/numerics/R2_EXACT_FACTORS_q1.json",
        "five_slowest_area_channels": ordered,
        "naive_three_term": naive,
        "five_rate_recurrence_characteristic_coefficients_ascending": co,
        "five_rate_recurrence_prediction_coefficients": recurrence_coefficients,
        "five_rate_recurrence_held_out": recurrence_predictions,
        "basis_amplitude_fits": amplitude_fits,
        "leading_constant_comparison": comparison,
        "explanation": [
            "The fitted ansatz has roots r,1,r^-1. The actual top-row data instead contain five slow decaying character-channel rates. Its four additional decaying channels beyond the leading one invalidate the assumed root set; the fitted constant and inverse-rate branches are spurious extrapolation artifacts.",
            "The fitted leading recurrence coefficient differs from 1+r+r^-1 by about 4.8e-7 relatively. Forming the R=28 prediction subtracts comparably huge terms, amplifying this small mode-mismatch into the observed 8.77e5 to 2.01e6 relative errors and sign reversals.",
            "The five-slowest-rate model predicts R=30,32,34 accurately and gives a full-area leading constant agreeing with the independent four-dominant-character calculation. The exact 16-by-16 companion has further branches, so nonzero held-out errors remain and this is not an exact finite Laurent proof. Interface rows and mode projection remain essential to any exact amplitude derivation."
        ],
        "qualification": "Non-interval numerical evidence only. No exact Laurent representation, RadiusDominantData certificate, amplitude closed form, physical seed, P3, or GoalNeg2 claim.",
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    (BASE / "R2_LAURENT_REVIEW.json").write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print(json.dumps(jsonable({"naive_three_term": naive,
                               "five_rate_recurrence_held_out": recurrence_predictions,
                               "leading_constant_comparison": comparison,
                               "peak_rss_KiB": result["peak_rss_KiB"]}), indent=2))


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=170)
    a = ap.parse_args()
    run(a.dps)
