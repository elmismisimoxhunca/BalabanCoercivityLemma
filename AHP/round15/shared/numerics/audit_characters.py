#!/usr/bin/env python3
"""Structural audit of all 336 exact-collar character artifacts."""
from pathlib import Path
import hashlib
import json
import sys
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"


def run():
    expected = {(1, 22): 16, (2, 20): 64, (4, 18): 256}
    rows = []
    ok = True
    for (q, R), count in expected.items():
        root = BASE / "characters" / f"q{q}_R{R}"
        index = json.loads((root / "INDEX.json").read_text())
        files = sorted(root.glob("c*_*.json"))
        local = len(files) == count
        for p in files:
            D = json.loads(p.read_text())
            local = local and D["q"] == q and D["R"] == R
            local = local and len(D["blocks"]) == 5
            local = local and all(len(M) == 12 and all(len(row) == 12 for row in M)
                                  for M in D["blocks"].values())
            local = local and D["reduced_determinants"]["A"] == D["reduced_determinants"]["C"]
            local = local and all(row["Kplus_deep_difference"] == "0.0" and
                                  row["K0_deep_difference"] == "0.0" and
                                  row["Kminus_deep_difference"] == "0.0"
                                  for row in D["constant_row_comparisons"]
                                  if row["x"] in (D["s"] + 1, D["s"] + 2, D["s"] + 5, D["hi"] - 2))
            key = f"{D['character'][0]}_{D['character'][1]}"
            recorded = index["characters"].get(key, {})
            local = local and recorded.get("sha256") == hashlib.sha256(p.read_bytes()).hexdigest()
        rows.append({"q": q, "R": R, "expected": count, "actual": len(files), "pass": local})
        ok = ok and local
    characteristic = []
    for q in (1, 2, 4):
        N = 4 * q
        for c in ("0_1", f"0_{N-1}", "1_0", f"{N-1}_0"):
            p = BASE / f"characteristic_q{q}_c{c}.json"
            D = json.loads(p.read_text())
            residual = sum(bool(z["terms"]) for z in D["factor_residual_highest_first"])
            characteristic.append({"q": q, "character": c, "factor_residual_terms": residual, "pass": residual == 0})
            ok = ok and residual == 0
    result = {"characters": rows, "characteristic": characteristic, "pass": ok,
              "qualification": "Structural and exact-arithmetic audit, not a physical area-seed proof."}
    (BASE / "CHARACTER_AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(run())
