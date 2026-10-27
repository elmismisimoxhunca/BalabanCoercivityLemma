#!/usr/bin/env python3
"""Exact characteristic polynomial and dominant factor of the collar pencil."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "AHP/round15/shared/numerics"))
from cyclotomic import Cyc, mat_zero, mat_mul, mat_inverse, mat_det
from fractions import Fraction
import argparse
import json
import mpmath as mp


def eye(N, n):
    return [[Cyc(N, {0: 1}) if i == j else Cyc(N) for j in range(n)] for i in range(n)]


def trace(A):
    return sum((A[i][i] for i in range(len(A))), Cyc(A[0][0].N))


def charpoly(T):
    n = len(T)
    N = T[0][0].N
    B = eye(N, n)
    coeffs = []
    for k in range(1, n + 1):
        B = mat_mul(T, B)
        c = -trace(B) / k
        coeffs.append(c)
        B = [[B[i][j] + (c if i == j else Cyc(N)) for j in range(n)] for i in range(n)]
    return [Cyc(N, {0: 1})] + coeffs


def poly_mul(a, b):
    out = [Cyc(a[0].N) for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = out[i + j] + x * y
    return out


def poly_sub(a, b):
    n = max(len(a), len(b))
    out = [Cyc(a[0].N) for _ in range(n)]
    for i in range(n):
        out[i] = (a[i] if i < len(a) else Cyc(a[0].N)) - (b[i] if i < len(b) else Cyc(a[0].N))
    return out


def poly_square(a):
    return poly_mul(a, a)


def poly_json(p):
    return [z.json() for z in p]


def run(path, out_path):
    mp.mp.dps = 100
    D = json.loads(Path(path).read_text())
    N = 4 * D["q"]
    def cyc(z):
        return Cyc(N, {int(k): Fraction(v) for k, v in z["terms"]})
    def mat(name):
        return [[cyc(z) for z in row] for row in D["reduced_blocks"][name]]
    A, B, C = mat("A"), mat("B"), mat("C")
    Ainv = mat_inverse(A)
    top_l = [[-z for z in row] for row in mat_mul(Ainv, B)]
    top_r = [[-z for z in row] for row in mat_mul(Ainv, C)]
    T = [top_l[i] + top_r[i] for i in range(8)] + [eye(N, 8)[i] + [Cyc(N) for _ in range(8)] for i in range(8)]
    cp = charpoly(T)
    # Dominant factor: (Q5^2-a^2*x^2)^2*(Q9^2-a^2*x^2)^2.
    a2 = Cyc(N, {0: 2, 1: 1, N - 1: 1})
    x2 = [Cyc(N), Cyc(N), Cyc(N, {0: 1})]
    q5 = poly_square([Cyc(N, {0: 1}), Cyc(N, {0: -5}), Cyc(N, {0: 1})])
    q9 = poly_square([Cyc(N, {0: 1}), Cyc(N, {0: -9}), Cyc(N, {0: 1})])
    a2x2 = [z * a2 for z in x2]
    f5 = poly_square(poly_sub(q5, a2x2))
    f9 = poly_square(poly_sub(q9, a2x2))
    candidate = poly_mul(f5, f9)
    residual = poly_sub(cp, candidate)
    result = {
        "source": str(path), "q": D["q"], "R": D["R"], "character": D["character"],
        "field": D["field"], "charpoly_highest_first": poly_json(cp),
        "dominant_factor_highest_first": poly_json(candidate),
        "factor_residual_highest_first": poly_json(residual),
        "a_squared": a2.json(),
        "factor_explanation": "Q5=x^2-5x+1, Q9=x^2-9x+1, a^2=2+zeta+zeta^(N-1); candidate=(Q5^2-a^2*x^2)^2*(Q9^2-a^2*x^2)^2",
        "detA": D["reduced_determinants"]["A"], "detC": D["reduced_determinants"]["C"],
        "qualification": "Exact arithmetic on the numerically transcribed collar matrices; not a Lean identification or an area-seed proof."
    }
    # With a^2=2+zeta+zeta^(N-1), the small-y channel is y=5-sqrt(a^2).
    sqrt_a2 = mp.sqrt(a2.numeric(110))
    y_numeric = 5 - sqrt_a2
    result["dominant_y"] = {"expression": "5 - sqrt(a_squared)",
                             "a_squared": a2.json(), "numeric": mp.nstr(y_numeric, 80)}
    discriminant_numeric = y_numeric ** 2 - 4
    result["dominant_discriminant"] = {"expression": "(5-sqrt(a_squared))^2-4",
                                        "numeric": mp.nstr(discriminant_numeric, 80)}
    Path(out_path).write_text(json.dumps(result, indent=2) + "\n")
    print("OUTPUT", out_path, "residual_terms", sum(bool(z.terms) for z in residual),
          "y", result["dominant_y"]["numeric"])


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    run(a.input, a.out)
