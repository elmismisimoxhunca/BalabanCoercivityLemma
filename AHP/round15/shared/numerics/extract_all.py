#!/usr/bin/env python3
"""Batch exact-collar extraction with resumable per-character artifacts."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "AHP/round15/shared/numerics"))
from exact_collar import run, jsonable
import argparse
import hashlib
import json
import time

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--R", type=int, required=True)
    ap.add_argument("--dps", type=int, default=70)
    ap.add_argument("--chars", default="all")
    ap.add_argument("--out", required=True)
    ap.add_argument("--drive")
    a = ap.parse_args()
    N = 4 * a.q
    chars = ([(iy, iz) for iy in range(N) for iz in range(N)] if a.chars == "all"
             else [tuple(map(int, s.split(":"))) for s in a.chars.split(",")])
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    index_path = out / "INDEX.json"
    old = json.loads(index_path.read_text()) if index_path.exists() else {"characters": {}}
    index = old
    index.update({"q": a.q, "R": a.R, "dps": a.dps, "drive": a.drive,
                  "qualification": "Exact cyclotomic operator transcription; optional residuals are non-interval numerical evidence only."})
    start = time.time()
    for iy, iz in chars:
        key = f"{iy}_{iz}"
        target = out / f"c{key}.json"
        if target.exists():
            try:
                D = json.loads(target.read_text())
                assert D["q"] == a.q and D["R"] == a.R and D["character"] == [iy, iz]
                assert D["dps"] == a.dps and D.get("reduced_blocks") and D.get("interface_rows")
                if a.drive is None or (D.get("solve") and D["solve"].get("drive") == a.drive):
                    print("REUSE", key, flush=True)
                    continue
            except Exception:
                pass
        result = run(a.q, a.R, iy, iz, a.q * (10 * a.R + 12) + 5, a.dps, a.drive)
        target.write_text(json.dumps(jsonable(result), indent=2) + "\n")
        index["characters"][key] = {
            "file": target.name, "sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
            "detA": result["reduced_determinants"]["A"].expression(),
            "detC": result["reduced_determinants"]["C"].expression(),
            "interface_rows": len(result["interface_rows"]),
            "solve_present": result["solve"] is not None,
        }
        index["seconds"] = time.time() - start
        index_path.write_text(json.dumps(index, indent=2) + "\n")
        print("CASE", key, "seconds", index["seconds"], flush=True)
    index["seconds"] = time.time() - start
    index_path.write_text(json.dumps(index, indent=2) + "\n")
    print("OUTPUT", index_path, "seconds", index["seconds"])
