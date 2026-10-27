#!/usr/bin/env python3
"""Attach completed per-character residual records to exact-collar artifacts."""
from pathlib import Path
import argparse
import hashlib
import json

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--characters", required=True)
    ap.add_argument("--sweep", required=True)
    a = ap.parse_args()
    root = Path(a.characters)
    D = json.loads(Path(a.sweep).read_text())
    index_path = root / "INDEX.json"
    index = json.loads(index_path.read_text())
    for rec in D["records"]:
        if rec["R"] != index["R"]:
            continue
        key = f"{rec['character'][0]}_{rec['character'][1]}"
        target = root / f"c{key}.json"
        if not target.exists():
            continue
        C = json.loads(target.read_text())
        C["solve"] = {
            "drive": D["drive"], "root": D["root"], "source_sweep": a.sweep,
            "flat_resolvent_absolute_residual": rec["flat_resolvent_absolute_residual"],
            "augmented_null_by_x": rec.get("augmented_null_by_x"),
            "augmented_null_max": rec.get("augmented_null_max"),
            "interface_values": rec.get("interface_values"),
            "qualification": "Non-interval residual record for the same flat augmented operator and drive; no interval proof."
        }
        target.write_text(json.dumps(C, indent=2) + "\n")
        index["characters"][key]["sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
        index["characters"][key]["solve_present"] = True
    index_path.write_text(json.dumps(index, indent=2) + "\n")
    print("OUTPUT", index_path)
