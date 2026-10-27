#!/usr/bin/env python3
"""Exact all-character collar determinant and characteristic-factor audit.

This consumes the retained round-15 R1 cyclotomic transcriptions.  It does not
assemble another physical operator and does not promote numerical identification
to a Lean theorem.  All new checks below use exact rational/cyclotomic arithmetic.

For zeta=exp(2*pi*i/N), put
  X = 2+zeta^iy+zeta^-iy, Z = 2+zeta^iz+zeta^-iz,
  L(t) = (t^2-7*t+1)^2.
The audited formulas are
  det(A)^-1 = (25-X-Z)^2-4*X*Z,
  chi_T(t) = ((L(t)-(X+Z)*t^2)^2-4*X*Z*t^4)^2.
Equivalently the four reciprocal-pair traces are 7 +/- x +/- z, where
x^2=X and z^2=Z; each pair occurs with multiplicity two.
"""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
SHARED = ROOT / "AHP/round15/shared/numerics"
sys.path.insert(0, str(SHARED))
from cyclotomic import Cyc, mat_mul, mat_inverse, mat_sub
from characteristic import charpoly, eye, poly_mul, poly_sub, poly_square
from fractions import Fraction
import argparse
import hashlib
import json
import mpmath as mp
import resource
import time
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def cyc(N, z):
    return Cyc(N, {int(k): Fraction(v) for k, v in z["terms"]})


def mat(N, rows):
    return [[cyc(N, z) for z in row] for row in rows]


def scale(p, c):
    return [z * c for z in p]


def zpow(N, k):
    return Cyc(N, {0: 1}) if k == 0 else Cyc(N, {k: 1})


def squared_cos(N, k):
    # (2*cos(pi*k/N))^2 = 2 + 2*cos(2*pi*k/N).
    return Cyc(N, {0: 2}) + zpow(N, k) + zpow(N, -k)


def is_exact_matrix(M, n=8):
    return (isinstance(M, list) and len(M) == n and
            all(isinstance(row, list) and len(row) == n and
                all(isinstance(z, dict) and "terms" in z for z in row) for row in M))


def reduce_from_12_blocks(D):
    """Recompute the exact Schur reduction, repairing R1's four q=4 A fields."""
    N = 4 * D["q"]
    A, B, C = (mat(N, D["blocks"][name]) for name in ("1", "0", "-1"))
    A00, A01 = [row[:4] for row in A[:4]], [row[4:] for row in A[:4]]
    A10, A11 = [row[:4] for row in A[4:]], [row[4:] for row in A[4:]]
    B00, B01 = [row[:4] for row in B[:4]], [row[4:] for row in B[:4]]
    B10, B11 = [row[:4] for row in B[4:]], [row[4:] for row in B[4:]]
    C00, C01 = [row[:4] for row in C[:4]], [row[4:] for row in C[:4]]
    C10, C11 = [row[:4] for row in C[4:]], [row[4:] for row in C[4:]]
    assert not any(z for row in A00 + C00 for z in row)
    assert not any(z for row in A10 + C01 for z in row)
    B00inv = mat_inverse(B00)
    ar = mat_sub(A11, mat_mul(mat_mul(B10, B00inv), A01))
    br = mat_sub(mat_sub(B11, mat_mul(mat_mul(B10, B00inv), B01)),
                 mat_mul(mat_mul(C10, B00inv), A01))
    cr = mat_sub(C11, mat_mul(mat_mul(C10, B00inv), B01))
    return ar, br, cr


def companion(A, B, C):
    N = A[0][0].N
    Ainv = mat_inverse(A)
    top_l = [[-z for z in row] for row in mat_mul(Ainv, B)]
    top_r = [[-z for z in row] for row in mat_mul(Ainv, C)]
    return ([top_l[i] + top_r[i] for i in range(8)] +
            [eye(N, 8)[i] + [Cyc(N) for _ in range(8)] for i in range(8)])


def sub_highest_first(a, b):
    """Subtract highest-first polynomials, right-aligning different degrees."""
    n = max(len(a), len(b))
    aa = [Cyc(a[0].N) for _ in range(n - len(a))] + list(a)
    bb = [Cyc(a[0].N) for _ in range(n - len(b))] + list(b)
    return [x - y for x, y in zip(aa, bb)]


def factor_formula(X, Z):
    N = X.N
    one = Cyc(N, {0: 1})
    t2 = [one, Cyc(N), Cyc(N)]
    t4 = [one, Cyc(N), Cyc(N), Cyc(N), Cyc(N)]
    L = poly_square([one, Cyc(N, {0: -7}), one])
    M = sub_highest_first(L, scale(t2, X + Z))
    base = sub_highest_first(poly_square(M), scale(t4, Cyc(N, {0: 4}) * X * Z))
    return poly_square(base)


def canonical_polynomial(p):
    return json.dumps([z.json() for z in p], sort_keys=True, separators=(",", ":"))


def nonzero_terms(p):
    return [{"coefficient_index_highest_first": i, "value": z.json()}
            for i, z in enumerate(p) if z]


def numeric_data(q, iy, iz, dps=110):
    old = mp.mp.dps
    mp.mp.dps = dps
    N = 4 * q
    x = 2 * mp.cos(mp.pi * iy / N)
    z = 2 * mp.cos(mp.pi * iz / N)
    ys = sorted([7 + sx * x + sz * z for sx in (-1, 1) for sz in (-1, 1)])
    # The uniform character's y=3 charged-area projection is absent in the
    # retained physical area data; its first surviving channel has y=7.
    s = mp.mpf(7) if (iy == 0 and iz == 0) else 7 - abs(x) - abs(z)
    rho = (s - mp.sqrt(s * s - 4)) / 2
    rate = rho ** (8 * q)
    ans = {"x_numeric": mp.nstr(x, 90), "z_numeric": mp.nstr(z, 90),
           "four_traces_numeric": [mp.nstr(y, 90) for y in ys],
           "area_trace_numeric": mp.nstr(s, 90),
           "area_rho_numeric": mp.nstr(rho, 90),
           "area_ratio_per_two_radius_numeric": mp.nstr(rate, 90),
           "uniform_y3_channel_suppressed": iy == 0 and iz == 0}
    mp.mp.dps = old
    return ans


def run(q, R, out_path, resume=True):
    start = time.time()
    root = SHARED / "characters" / f"q{q}_R{R}"
    paths = sorted(root.glob("c*_*.json"), key=lambda p: tuple(map(int, p.stem[1:].split("_"))))
    assert len(paths) == (4 * q) ** 2
    partial = Path(out_path + ".partial.json")
    done = {}
    if resume and partial.exists():
        old = json.loads(partial.read_text())
        assert old["q"] == q and old["R"] == R
        done = {tuple(r["character"]): r for r in old["records"]}
        print("RESUME", len(done), flush=True)
    records = []
    for p in paths:
        raw = p.read_bytes()
        D = json.loads(raw)
        iy, iz = D["character"]
        source_hash = hashlib.sha256(raw).hexdigest()
        key = (iy, iz)
        if key in done and done[key]["source_sha256"] == source_hash:
            rec = done[key]
            records.append(rec)
            print("REUSE", q, key, flush=True)
            continue
        N = 4 * q
        repair = None
        if all(is_exact_matrix(D["reduced_blocks"][name]) for name in ("A", "B", "C")):
            A, B, C = (mat(N, D["reduced_blocks"][name]) for name in ("A", "B", "C"))
        else:
            # R1's four dominant q=4 JSON files accidentally store a numeric
            # string in reduced_blocks.A.  The exact 12-block source is intact.
            assert q == 4 and key in {(0, 1), (0, N - 1), (1, 0), (N - 1, 0)}
            assert not is_exact_matrix(D["reduced_blocks"]["A"])
            assert is_exact_matrix(D["reduced_blocks"]["B"])
            assert is_exact_matrix(D["reduced_blocks"]["C"])
            A, Br, Cr = reduce_from_12_blocks(D)
            B = mat(N, D["reduced_blocks"]["B"])
            C = mat(N, D["reduced_blocks"]["C"])
            assert Br == B and Cr == C
            repair = {"defect": "R1 reduced_blocks.A is not an exact 8x8 matrix",
                      "method": "recomputed A,B,C from retained exact 12-block matrices by the R1 Schur formula; recomputed B and C equal the retained matrices exactly",
                      "reconstructed_A_equals_retained_C": A == C}
        assert all(len(M) == 8 and all(len(row) == 8 for row in M) for M in (A, B, C))
        X, Z = squared_cos(N, iy), squared_cos(N, iz)
        det_base = Cyc(N, {0: 25}) - X - Z
        predicted_inverse = det_base * det_base - Cyc(N, {0: 4}) * X * Z
        det_a, det_c = cyc(N, D["reduced_determinants"]["A"]), cyc(N, D["reduced_determinants"]["C"])
        det_residual = det_a * predicted_inverse - Cyc(N, {0: 1})
        det_ac_residual = det_a - det_c
        ac_residual = mat_sub(A, C)
        T = companion(A, B, C)
        cp = charpoly(T)
        factor = factor_formula(X, Z)
        residual = poly_sub(cp, factor)
        rec = {
            "character": [iy, iz], "source": str(p.relative_to(ROOT)),
            "source_sha256": source_hash,
            "X": X.json(), "Z": Z.json(),
            "detA": det_a.json(), "detC": det_c.json(),
            "predicted_detA_inverse": predicted_inverse.json(),
            "detA_times_predicted_inverse_minus_one": det_residual.json(),
            "detA_minus_detC": det_ac_residual.json(),
            "reduced_A_minus_C": [[z.json() for z in row] for row in ac_residual],
            "source_repair": repair,
            "charpoly_minus_factor": nonzero_terms(residual),
            "charpoly_sha256": hashlib.sha256(canonical_polynomial(cp).encode()).hexdigest(),
            "factor_sha256": hashlib.sha256(canonical_polynomial(factor).encode()).hexdigest(),
            **numeric_data(q, iy, iz),
        }
        assert (not det_residual and not det_ac_residual and not any(residual) and
                not any(z for row in ac_residual for z in row)), (q, key)
        records.append(rec)
        partial.write_text(json.dumps({"q": q, "R": R, "records": records}, indent=2) + "\n")
        print("EXACT", q, key, "elapsed", time.time() - start, flush=True)
    assert len(records) == len(paths)
    groups = {}
    for rec in records:
        key = json.dumps([rec["X"]["terms"], rec["Z"]["terms"]], sort_keys=True)
        groups.setdefault(key, {"X": rec["X"], "Z": rec["Z"],
                                "predicted_detA_inverse": rec["predicted_detA_inverse"],
                                "factor_sha256": rec["factor_sha256"], "characters": []})
        groups[key]["characters"].append(rec["character"])
    # Publish one explicit polynomial per distinct (X,Z), rather than repeating
    # identical long polynomials for conjugate characters.
    group_list = []
    for group in groups.values():
        X, Z = cyc(4 * q, group["X"]), cyc(4 * q, group["Z"])
        factor = factor_formula(X, Z)
        assert hashlib.sha256(canonical_polynomial(factor).encode()).hexdigest() == group["factor_sha256"]
        group_list.append(group | {"factor_highest_first": [z.json() for z in factor]})
    group_list.sort(key=lambda g: g["characters"])
    repairs = [r for r in records if r["source_repair"] is not None]
    result = {
        "q": q, "R": R, "character_count": len(records), "distinct_XZ_count": len(group_list),
        "source_repair_count": len(repairs),
        "source_repair_characters": [r["character"] for r in repairs],
        "formula": {
            "zeta": "exp(2*pi*i/(4q))",
            "X": "2+zeta^iy+zeta^-iy = (2*cos(pi*iy/(4q)))^2",
            "Z": "2+zeta^iz+zeta^-iz = (2*cos(pi*iz/(4q)))^2",
            "detA_inverse": "(25-X-Z)^2-4*X*Z",
            "charpoly": "((L-(X+Z)*t^2)^2-4*X*Z*t^4)^2, L=(t^2-7*t+1)^2",
            "trace_form": "each t^2-(7+s1*x+s2*z)*t+1, s1,s2 in {-1,1}, occurs squared; x^2=X,z^2=Z",
            "area_rate": "rho=(s-sqrt(s^2-4))/2, s=7-abs(x)-abs(z); ratio per R->R+2 is rho^(8q). At (0,0), the y=3 charged-area channel is suppressed and s=7 is used, matching retained data."
        },
        "records": records, "distinct_factors": group_list,
        "seconds": time.time() - start,
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "qualification": "Exact arithmetic on the retained numerically transcribed frozen-family matrices. All 12-block dictionaries and interface rows remain those of R1. No interval solve, physical Lean identification, amplitude closed form, area seed, spectral-gap proof, or GoalNeg2 claim."
    }
    Path(out_path).write_text(json.dumps(result, indent=2) + "\n")
    print("OUTPUT", out_path, "characters", len(records), "groups", len(group_list),
          "seconds", result["seconds"], "peak_rss_KiB", result["peak_rss_KiB"], flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True, choices=(1, 2, 4))
    ap.add_argument("--R", type=int, default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--no-resume", action="store_true")
    a = ap.parse_args()
    run(a.q, a.R if a.R is not None else {1: 22, 2: 20, 4: 18}[a.q], a.out, not a.no_resume)
