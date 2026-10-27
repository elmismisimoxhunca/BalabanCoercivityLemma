#!/usr/bin/env python3
"""Final structural and exact-arithmetic audit for round-15 numerics R2."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"
LOCAL = ROOT / "AHP/round15/numerics/r2"
sys.path.insert(0, str(BASE))
sys.path.insert(0, str(LOCAL))
from cyclotomic import Cyc
from exact_factors import is_exact_matrix
from fractions import Fraction
import hashlib
import json
import mpmath as mp


def cyc(N, z):
    return Cyc(N, {int(k): Fraction(v) for k, v in z["terms"]})


def zero_json(z):
    return not z["terms"]


def matrix_json_zero(M):
    return all(zero_json(z) for row in M for z in row)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def poly_hash(p):
    return hashlib.sha256(json.dumps(p, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def run():
    mp.mp.dps = 100
    expected = {(1, 22): 16, (2, 20): 64, (4, 18): 256}
    malformed_expected = {(4, 0, 1), (4, 0, 15), (4, 1, 0), (4, 15, 0)}
    source_rows, factor_rows = [], []
    ok = True
    for (q, R), count in expected.items():
        root = BASE / f"characters/q{q}_R{R}"
        index = json.loads((root / "INDEX.json").read_text())
        paths = sorted(root.glob("c*_*.json"))
        malformed, solve_residuals, null_residuals = [], [], []
        interface_rows = 0
        local = len(paths) == count
        for p in paths:
            raw = p.read_bytes()
            D = json.loads(raw)
            iy, iz = D["character"]
            local = local and sha(p) == index["characters"][f"{iy}_{iz}"]["sha256"]
            local = local and D["q"] == q and D["R"] == R
            local = local and len(D["blocks"]) == 5
            local = local and all(is_exact_matrix(D["blocks"][k], 12) for k in ("-2", "-1", "0", "1", "2"))
            local = local and bool(D["interface_rows"])
            interface_rows += len(D["interface_rows"])
            for name in ("B", "C"):
                local = local and is_exact_matrix(D["reduced_blocks"][name], 8)
            if not is_exact_matrix(D["reduced_blocks"]["A"], 8):
                malformed.append([iy, iz])
            for row in D["constant_row_comparisons"]:
                if row["x"] in (D["s"] + 1, D["s"] + 2, D["s"] + 5, D["hi"] - 2):
                    local = local and all(row[k] == "0.0" for k in
                                          ("Kplus_deep_difference", "K0_deep_difference", "Kminus_deep_difference"))
            solve = D.get("solve")
            if solve:
                solve_residuals.append(mp.mpf(solve["flat_resolvent_absolute_residual"]))
                if solve.get("augmented_null_max") is not None:
                    null_residuals.append(mp.mpf(solve["augmented_null_max"]))
        expected_bad = sorted([list(x[1:]) for x in malformed_expected if x[0] == q])
        local = local and sorted(malformed) == expected_bad
        source_rows.append({"q": q, "R": R, "characters": len(paths),
                            "interface_rows": interface_rows,
                            "malformed_reduced_A_characters": malformed,
                            "solve_record_count": len(solve_residuals),
                            "max_flat_resolvent_absolute_residual": mp.nstr(max(solve_residuals), 12) if solve_residuals else None,
                            "augmented_null_record_count": len(null_residuals),
                            "max_augmented_null_available": mp.nstr(max(null_residuals), 12) if null_residuals else None,
                            "pass": local})
        ok = ok and local
        F = json.loads((BASE / f"R2_EXACT_FACTORS_q{q}.json").read_text())
        local = F["character_count"] == count and len(F["records"]) == count
        local = local and F["source_repair_count"] == len(expected_bad)
        for rec in F["records"]:
            iy, iz = rec["character"]
            N = 4 * q
            X, Z = cyc(N, rec["X"]), cyc(N, rec["Z"])
            base = Cyc(N, {0: 25}) - X - Z
            predicted = base * base - Cyc(N, {0: 4}) * X * Z
            det = cyc(N, rec["detA"])
            local = local and predicted == cyc(N, rec["predicted_detA_inverse"])
            local = local and det * predicted == Cyc(N, {0: 1})
            local = local and det == cyc(N, rec["detC"])
            local = local and zero_json(rec["detA_times_predicted_inverse_minus_one"])
            local = local and zero_json(rec["detA_minus_detC"])
            local = local and matrix_json_zero(rec["reduced_A_minus_C"])
            local = local and not rec["charpoly_minus_factor"]
            source = ROOT / rec["source"]
            local = local and sha(source) == rec["source_sha256"]
            c = f"{iy}_{iz}"
            old_path = BASE / f"characteristic_q{q}_c{c}.json"
            if old_path.exists():
                old = json.loads(old_path.read_text())
                local = local and poly_hash(old["charpoly_highest_first"]) == rec["charpoly_sha256"]
        factor_rows.append({"q": q, "characters": F["character_count"],
                            "distinct_XZ": F["distinct_XZ_count"],
                            "source_repair_characters": F["source_repair_characters"],
                            "all_determinant_identities_exact": local,
                            "all_characteristic_factor_residuals_zero": all(not r["charpoly_minus_factor"] for r in F["records"]),
                            "pass": local})
        ok = ok and local
    repair_index_path = BASE / "R2_repaired/q4_R18/INDEX.json"
    repair_index = json.loads(repair_index_path.read_text())
    repair_ok = set(repair_index["characters"]) == {"0_1", "0_15", "1_0", "15_0"}
    for key, rec in repair_index["characters"].items():
        source, repaired = ROOT / rec["source"], ROOT / rec["repaired"]
        O, D = json.loads(source.read_text()), json.loads(repaired.read_text())
        repair_ok = repair_ok and sha(source) == rec["source_sha256"]
        repair_ok = repair_ok and sha(repaired) == rec["repaired_sha256"]
        repair_ok = repair_ok and D["r2_repair"]["source_sha256"] == rec["source_sha256"]
        repair_ok = repair_ok and all(is_exact_matrix(D["reduced_blocks"][name], 8) for name in ("A", "B", "C"))
        repair_ok = repair_ok and D["reduced_blocks"]["A"] == D["reduced_blocks"]["C"]
        repair_ok = repair_ok and D["reduced_blocks"]["B"] == O["reduced_blocks"]["B"]
        repair_ok = repair_ok and D["reduced_blocks"]["C"] == O["reduced_blocks"]["C"]
        repair_ok = repair_ok and D["blocks"] == O["blocks"] and D["interface_rows"] == O["interface_rows"]
    ok = ok and repair_ok
    closed = json.loads((BASE / "R2_CLOSED_FORM.json").read_text())
    closed_ok = len(closed["determinants"]) == 115 and len(closed["summary"]) == 3
    closed_ok = closed_ok and all(x["relation"] is None for x in closed["leading_amplitude_bounded_search"])
    closed_ok = closed_ok and "not in Q(sqrt(2))" in closed["summary"][2]["qsqrt2_obstruction"]
    ok = ok and closed_ok
    leading = json.loads((BASE / "R2_LEADING_STABILITY.json").read_text())
    leading_rows = []
    for row in leading["rows"]:
        vals = [mp.mpf(r["normalized_leading_constant"]) for r in row["table"]]
        diffs = [abs(mp.mpf(r["stored_normalized_minus_recomputed"])) for r in row["table"]]
        local = [r["R"] for r in row["table"]] == list(range(18, 42, 2))
        local = local and len(vals) == 12 and all(v != 0 for v in vals)
        local = local and max(diffs) < mp.mpf("1e-60") and row["record_count"] == 48
        leading_rows.append({"q": row["q"], "K_R18": row["K_R18"], "K_R40": row["K_R40"],
                             "K_R40_over_K_R18_minus_one": row["K_R40_over_K_R18_minus_one"],
                             "max_stored_minus_recomputed": mp.nstr(max(diffs), 8), "pass": local})
        ok = ok and local
    laurent = json.loads((BASE / "R2_LAURENT_REVIEW.json").read_text())
    laurent_ok = all(laurent["naive_three_term"][str(d)]["sign_reversed"] and
                     mp.mpf(laurent["naive_three_term"][str(d)]["held_out_relative_error"]) > mp.mpf("1e5")
                     for d in range(3))
    laurent_ok = laurent_ok and all(mp.mpf(laurent["five_rate_recurrence_held_out"]["1"][str(R)]["relative_error"]) < mp.mpf("1e-25")
                                    for R in (30, 32, 34))
    laurent_ok = laurent_ok and abs(mp.mpf(laurent["leading_constant_comparison"]["relative_difference"])) < mp.mpf("1e-18")
    ok = ok and laurent_ok
    result = {
        "pass": ok, "source_dictionaries": source_rows, "exact_factors": factor_rows,
        "repaired_q4_files": {"count": len(repair_index["characters"]), "pass": repair_ok},
        "closed_form": {"distinct_determinant_records": len(closed["determinants"]),
                        "bounded_amplitude_relations_found": [x for x in closed["leading_amplitude_bounded_search"] if x["relation"] is not None],
                        "pass": closed_ok},
        "leading_stability": leading_rows,
        "laurent_review": {"naive_sign_reversals": [laurent["naive_three_term"][str(d)]["sign_reversed"] for d in range(3)],
                           "naive_held_out_relative_errors": [laurent["naive_three_term"][str(d)]["held_out_relative_error"] for d in range(3)],
                           "five_rate_tangential_held_out_errors": [laurent["five_rate_recurrence_held_out"]["1"][str(R)]["relative_error"] for R in (30, 32, 34)],
                           "leading_constant_relative_difference": laurent["leading_constant_comparison"]["relative_difference"],
                           "pass": laurent_ok},
        "field_correction": "Q(zeta16) has degree 8 over Q; its maximal real subfield has degree 4. The q=4 dominant det(A)^-1 is not in Q(sqrt2).",
        "qualification": "R2 exact arithmetic is on numerically transcribed frozen-family matrices. All area values and residuals are non-interval evidence. No Lean declaration, physical seed, normalized matrix limit, or GoalNeg2 proof is claimed."
    }
    payload = json.dumps(result, indent=2) + "\n"
    (LOCAL / "AUDIT.json").write_text(payload)
    (BASE / "R2_AUDIT.json").write_text(payload)
    print(json.dumps({"pass": ok, "source_dictionaries": source_rows,
                      "exact_factors": factor_rows, "repaired_q4_files": result["repaired_q4_files"],
                      "closed_form": result["closed_form"], "leading_stability": leading_rows,
                      "laurent_review": result["laurent_review"]}, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(run())
