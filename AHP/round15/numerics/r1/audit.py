#!/usr/bin/env python3
"""Final audit for the round-15 numerics track (evidence only)."""
from pathlib import Path
import hashlib
import json
import sys
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"


def main():
    checks = {}
    character_audit = json.loads((BASE / "CHARACTER_AUDIT.json").read_text())
    checks["all_336_operator_dictionaries"] = character_audit["pass"]
    laurent = json.loads((BASE / "LAURENT_REVIEW.json").read_text())
    checks["naive_laurent_failure_reproduced"] = all(
        float(row["held_out_relative_error"]) > 100000 for row in laurent["naive_three_term"].values())
    checks["five_rate_held_out_explanation"] = all(
        float(row["relative_error"]) < 1e-8 for row in laurent["full_recurrence_R34"].values())
    summary = json.loads((BASE / "LEADING_SUMMARY.json").read_text())
    checks["q1_q2_q4_rates_and_constants"] = [row["q"] for row in summary["rows"]] == [1, 2, 4]
    checks["characteristic_factor_zero"] = all(
        row["characteristic_factor_residual_terms"] == 0 for row in summary["rows"])
    checks["normalized_constants_stable"] = all(
        abs(float(row["normalized_R18_to_R40_relative_change"])) < 1e-8 for row in summary["rows"])
    files = [BASE / "README.md", BASE / "LEADING_SUMMARY.json", BASE / "LAURENT_REVIEW.json",
             BASE / "CHARACTER_AUDIT.json", BASE / "cyclotomic.py", BASE / "exact_collar.py",
             BASE / "characteristic.py", BASE / "dominant_sweep.py", BASE / "leading_summary.py"]
    result = {"checks": checks, "pass": all(checks.values()),
              "files": [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in files],
              "qualification": "Numerical evidence only; no Lean or interval certificate is claimed."}
    (ROOT / "AHP/round15/numerics/r1/AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
