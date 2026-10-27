#!/usr/bin/env python3
"""Deduplicate augmented-variable descriptors across character files."""
from pathlib import Path
import argparse
import hashlib
import json

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--characters", required=True)
    a = ap.parse_args()
    root = Path(a.characters)
    files = sorted(root.glob("c*_*.json"))
    if not files:
        raise SystemExit("no character files")
    first = json.loads(files[0].read_text())
    descriptors = first.get("descriptors")
    if descriptors is None:
        descriptors = json.loads((root / first.get("descriptor_file", "descriptors.json")).read_text())
    (root / "descriptors.json").write_text(json.dumps(descriptors, indent=2) + "\n")
    index_path = root / "INDEX.json"
    index = json.loads(index_path.read_text())
    for p in files:
        D = json.loads(p.read_text())
        D.pop("descriptors", None)
        D["descriptor_file"] = "descriptors.json"
        p.write_text(json.dumps(D, indent=2) + "\n")
        key = f"{D['character'][0]}_{D['character'][1]}"
        index["characters"][key]["sha256"] = hashlib.sha256(p.read_bytes()).hexdigest()
    index["descriptor_file"] = "descriptors.json"
    index_path.write_text(json.dumps(index, indent=2) + "\n")
    print("OUTPUT", index_path)
