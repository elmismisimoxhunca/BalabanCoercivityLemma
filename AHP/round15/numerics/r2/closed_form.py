#!/usr/bin/env python3
"""Closed-form determinant fields and a bounded amplitude-relation search.

Exact determinant arithmetic is separated from non-proof PSLQ evidence about the
area amplitude.  A failed PSLQ search is not a nonexistence theorem.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"
sys.path.insert(0, str(BASE))
from cyclotomic import Cyc
from fractions import Fraction
import json
import mpmath as mp
import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def cyc(N, z):
    return Cyc(N, {int(k): Fraction(v) for k, v in z["terms"]})


def quad(a=0, b=0):
    return (Fraction(a), Fraction(b))


def qadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def qscale(c, x):
    return (c * x[0], c * x[1])


def qstr(x):
    a, b = x
    if not b:
        return str(a)
    return f"{a} + ({b})*sqrt(2)"


def real_quadratic(N, z):
    """Return exact real/imaginary parts; q=1 uses Q, q=2 uses Q(sqrt2)."""
    z = cyc(N, z) if isinstance(z, dict) else z
    re = im = quad()
    for k, c in z.terms.items():
        if N == 4:
            table = {0: (quad(1), quad()), 1: (quad(), quad(1))}
        elif N == 8:
            table = {
                0: (quad(1), quad()),
                1: (quad(0, Fraction(1, 2)), quad(0, Fraction(1, 2))),
                2: (quad(), quad(1)),
                3: (quad(0, -Fraction(1, 2)), quad(0, Fraction(1, 2))),
            }
        else:
            raise ValueError(N)
        rr, ii = table[k]
        re = qadd(re, qscale(c, rr))
        im = qadd(im, qscale(c, ii))
    return re, im


def numeric_cyc(N, z, dps=100):
    return cyc(N, z).numeric(dps)


def run():
    start_dps = mp.mp.dps
    mp.mp.dps = 100
    rows = []
    determinant_records = []
    for q in (1, 2, 4):
        D = json.loads((BASE / f"R2_EXACT_FACTORS_q{q}.json").read_text())
        assert D["character_count"] == (4 * q) ** 2
        assert all(not r["charpoly_minus_factor"] for r in D["records"])
        assert all(not r["detA_times_predicted_inverse_minus_one"]["terms"] for r in D["records"])
        assert all(not r["detA_minus_detC"]["terms"] for r in D["records"])
        assert all(not any(z["terms"] for z in row) for r in D["records"] for row in r["reduced_A_minus_C"])
        for group in D["distinct_factors"]:
            item = {"q": q, "characters": group["characters"],
                    "detA_inverse_cyclotomic": group["predicted_detA_inverse"]}
            sample = next(r for r in D["records"] if r["character"] == group["characters"][0])
            item["detA_cyclotomic"] = sample["detA"]
            if q in (1, 2):
                inv_re, inv_im = real_quadratic(4 * q, group["predicted_detA_inverse"])
                det_re, det_im = real_quadratic(4 * q, sample["detA"])
                assert not inv_im[0] and not inv_im[1] and not det_im[0] and not det_im[1]
                item["detA_inverse_real_closed_form"] = qstr(inv_re)
                item["detA_real_closed_form"] = qstr(det_re)
                if q == 1:
                    assert not inv_re[1] and not det_re[1]
            determinant_records.append(item)
        c01 = next(r for r in D["records"] if r["character"] == [0, 1])
        row = {"q": q, "characters": D["character_count"],
               "distinct_XZ": D["distinct_XZ_count"], "source_repair_count": D["source_repair_count"],
               "dominant_detA_inverse": c01["predicted_detA_inverse"],
               "dominant_detA": c01["detA"]}
        if q == 1:
            row["dominant_closed_form"] = "det(A)=1/329; det(A)^-1=329"
        elif q == 2:
            row["dominant_closed_form"] = "det(A)^-1=331-54*sqrt(2); det(A)=(331+54*sqrt(2))/103729"
            assert row["dominant_detA_inverse"] is not None
        else:
            # u=2*cos(pi/8)=sqrt(2+sqrt(2)); X=4, Z=2+u at c=(0,1).
            u = mp.sqrt(2 + mp.sqrt(2))
            predicted = 329 + u * u - 54 * u
            actual = numeric_cyc(16, c01["predicted_detA_inverse"], 110)
            assert abs(predicted - actual) < mp.mpf("1e-90")
            row["dominant_closed_form"] = "u=sqrt(2+sqrt(2)); det(A)^-1=329+u^2-54*u=331+sqrt(2)-54*u; det(A)=1/(331+sqrt(2)-54*u)"
            row["qsqrt2_obstruction"] = "The nonzero coefficient -54 on u and u^2=2+sqrt(2) would force u in Q(sqrt(2)) if det(A)^-1 were in Q(sqrt(2)). But u=sqrt(2+sqrt(2)) has degree 4 over Q. Thus this dominant q=4 determinant is not in Q(sqrt(2))."
        rows.append(row)
    leading = json.loads((BASE / "LEADING_SUMMARY.json").read_text())
    amplitude_tests = []
    for row in leading["rows"]:
        q = row["q"]
        K = mp.mpf(row["normalized_constant_R40"])
        relation = mp.pslq([mp.mpf(1), mp.sqrt(2), K], tol=mp.mpf("1e-45"),
                           maxcoeff=10**9, maxsteps=200000)
        amplitude_tests.append({
            "q": q, "K_R40": mp.nstr(K, 75),
            "basis": ["1", "sqrt(2)", "K"], "coefficient_bound": 10**9,
            "tol": "1e-45", "relation": relation,
            "interpretation": "No small Q(sqrt2) relation was found if relation is null. This bounded floating-point search is not a proof of nonexistence and is not an exact amplitude formula."
        })
    result = {
        "formula": "X=2+zeta^iy+zeta^-iy, Z=2+zeta^iz+zeta^-iz; det(A)^-1=(25-X-Z)^2-4*X*Z",
        "fields": {
            "q1": "All exact collar entries are Gaussian rational; the audited determinants and inverses are rational.",
            "q2": "Entries are in Q(zeta8)=Q(i,sqrt2). Real determinant values are converted explicitly to Q(sqrt2).",
            "q4": "Entries are in Q(zeta16), whose degree over Q is 8 (not 4). Its maximal real subfield is Q(u), u=2*cos(pi/8)=sqrt(2+sqrt2), of degree 4. Exact cyclotomic forms are retained; no false Q(sqrt2) claim is made."
        },
        "summary": rows, "determinants": determinant_records,
        "leading_amplitude_bounded_search": amplitude_tests,
        "amplitude_status": "No exact rational or Q(sqrt2) closed form for the physical leading area amplitude is established. The exact rate and determinant formulas do not determine the amplitude: it also involves the star/Omega1 interfaces, the nine-bond crossing drive, mode projection, and the quadratic dressed-jet observable.",
        "qualification": "Exact rational/cyclotomic determinant arithmetic plus explicitly bounded, non-proof numerical relation searches. No interval certificate or Lean/area-seed claim.",
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    (BASE / "R2_CLOSED_FORM.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"summary": rows, "leading_amplitude_bounded_search": amplitude_tests,
                      "determinant_record_count": len(determinant_records),
                      "peak_rss_KiB": result["peak_rss_KiB"]}, indent=2))
    mp.mp.dps = start_dps


if __name__ == "__main__":
    run()
