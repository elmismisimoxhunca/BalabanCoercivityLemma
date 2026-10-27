#!/usr/bin/env python3
"""Publish exact R2 repairs for four malformed R1 q=4 reduced-A fields.

The original R1 files are read-only evidence.  Repaired copies are written under
shared/numerics/R2_repaired and retain the original source hash and repair note.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "AHP/round15/shared/numerics"
sys.path.insert(0, str(ROOT / "AHP/round15/numerics/r2"))
from exact_factors import reduce_from_12_blocks, is_exact_matrix, mat
import hashlib
import json
import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def run():
    q, R, N = 4, 18, 16
    source_root = BASE / "characters/q4_R18"
    out_root = BASE / "R2_repaired/q4_R18"
    out_root.mkdir(parents=True, exist_ok=True)
    index = {"q": q, "R": R, "characters": {},
             "qualification": "Exact Schur reconstruction from retained 12-block matrices. Original R1 files are unchanged; numerical physical identification is still not a Lean proof."}
    for iy, iz in ((0, 1), (0, 15), (1, 0), (15, 0)):
        source = source_root / f"c{iy}_{iz}.json"
        raw = source.read_bytes()
        D = json.loads(raw)
        assert not is_exact_matrix(D["reduced_blocks"]["A"])
        assert is_exact_matrix(D["reduced_blocks"]["B"])
        assert is_exact_matrix(D["reduced_blocks"]["C"])
        A, B, C = reduce_from_12_blocks(D)
        assert B == mat(N, D["reduced_blocks"]["B"])
        assert C == mat(N, D["reduced_blocks"]["C"])
        assert A == C
        D["reduced_blocks"]["A"] = [[z.json() for z in row] for row in A]
        source_hash = hashlib.sha256(raw).hexdigest()
        D["r2_repair"] = {
            "source": str(source.relative_to(ROOT)), "source_sha256": source_hash,
            "defect": "R1 reduced_blocks.A was a numeric string rather than an exact 8x8 cyclotomic matrix",
            "method": "Recomputed A,B,C from the retained exact blocks[1],blocks[0],blocks[-1] using the original direction-zero Schur formula. Recomputed B and C equal retained B and C exactly; A equals C exactly."
        }
        target = out_root / source.name
        target.write_text(json.dumps(D, indent=2) + "\n")
        repaired_hash = hashlib.sha256(target.read_bytes()).hexdigest()
        index["characters"][f"{iy}_{iz}"] = {
            "source": str(source.relative_to(ROOT)), "source_sha256": source_hash,
            "repaired": str(target.relative_to(ROOT)), "repaired_sha256": repaired_hash,
            "reconstructed_A_equals_C": True,
            "recomputed_B_and_C_match_retained_exactly": True,
        }
        print("REPAIRED", source, "->", target, flush=True)
    (out_root / "INDEX.json").write_text(json.dumps(index, indent=2) + "\n")
    print("OUTPUT", out_root / "INDEX.json", "peak_rss_KiB",
          resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


if __name__ == "__main__":
    run()
