#!/usr/bin/env python3
"""Direct dominant-character right-star areas and normalized leading constants.

Only four characters per q are needed for the slowest decaying channel.  The
script reuses compatible completed sweeps and solves every missing radius
independently; it never treats a fitted rate as a proof.
"""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "AHP/round6/probe"))
from probe import mp, jsonable
sys.path.insert(0, str(ROOT / "AHP/round15/numerics/r1"))
from area_sweep import solve_character
sys.path.insert(0, str(ROOT / "AHP/round14/assembly/r2"))
from right_star import geometry
import argparse
import json
import resource
import time
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def dominant_characters(q):
    N = 4 * q
    return [(0, 1), (0, N - 1), (1, 0), (N - 1, 0)]


def run(q, radii, dps, drive_path, reuse_paths, out_path):
    mp.mp.dps = dps
    chars = dominant_characters(q)
    raw = json.loads(Path(drive_path).read_text())
    drive = []
    for s in raw["z"]:
        p = s.strip().strip("()").split()
        if len(p) == 2:
            drive.append(mp.mpc(mp.mpf(p[0]), mp.mpf(p[1][:-1])))
        else:
            drive.append(mp.mpc(mp.mpf(p[0]), mp.mpf(p[1] + p[2][:-1])))
    records = {}
    cache_path = Path(out_path + ".records.json")
    if cache_path.exists():
        for rec in json.loads(cache_path.read_text()):
            key = (rec["R"], tuple(rec["character"]))
            if key[1] in chars and key[0] in radii and rec.get("source_drive", drive_path) == drive_path:
                records[key] = rec
        print("REUSE_CACHE", cache_path, "records", len(records), flush=True)
    for path in reuse_paths:
        p = Path(path)
        if not p.exists():
            continue
        D = json.loads(p.read_text())
        if D.get("q") != q or D.get("drive") != drive_path:
            continue
        for rec in D.get("records", []):
            key = (rec["R"], tuple(rec["character"]))
            if key[1] in chars and key[0] in radii:
                records[key] = rec
        print("REUSE_SOURCE", path, "records", len(records), flush=True)
    start = time.time()
    for R in radii:
        boundary = q * (12 * R + 12)
        _, bonds = geometry(boundary, "right")
        for c in chars:
            key = (R, c)
            if key not in records:
                records[key] = solve_character(q, R, c[0], c[1], drive, bonds, dps)
                records[key]["R"] = R
                records[key]["character"] = list(c)
                records[key]["source_drive"] = drive_path
                cache_path.write_text(json.dumps(jsonable(list(records.values())), indent=2) + "\n")
                print("CASE", q, R, c, "area", mp.nstr(records[key]["sector_areaSum"], 12),
                      "seconds", time.time() - start, flush=True)
            else:
                print("REUSE", q, R, c, flush=True)
    N = 4 * q
    cy = {c: mp.cos(mp.pi * c[0] / N) for c in chars}
    cz = {c: mp.cos(mp.pi * c[1] / N) for c in chars}
    s = {c: 7 - 2 * (abs(cy[c]) + abs(cz[c])) for c in chars}
    rho = {c: (s[c] - mp.sqrt(s[c] ** 2 - 4)) / 2 for c in chars}
    rate = {c: rho[c] ** (8 * q) for c in chars}
    assert len(set(mp.nstr(rate[c], 60) for c in chars)) == 1
    dominant_rate = next(iter(rate.values()))
    table = []
    for R in radii:
        sector = {c: mp.mpf(records[(R, c)]["sector_areaSum"]) for c in chars}
        area = sum(sector.values()) / (N * N)
        normalized = area / dominant_rate ** (mp.mpf(R) / 2)
        row = {"R": R, "areaSum_dominant_characters": area,
               "normalized_leading_constant": normalized,
               "per_character": []}
        for c in chars:
            rec = records[(R, c)]
            previous = records.get((R - 2, c))
            previous_area = mp.mpf(previous["sector_areaSum"]) if previous else None
            row["per_character"].append({
                "character": list(c), "s": s[c], "rho": rho[c],
                "expected_area_ratio_per_two_radius": rate[c],
                "sector_areaSum": sector[c],
                "measured_ratio_per_two_radius": (sector[c] / previous_area
                                                   if previous else None),
                "ratio_relative_error": (sector[c] / previous_area / rate[c] - 1
                                          if previous else None),
                "normalized_sector_constant": sector[c] / dominant_rate ** (mp.mpf(R) / 2),
                "flat_resolvent_absolute_residual": rec.get("flat_resolvent_absolute_residual"),
                "augmented_null_max": rec.get("augmented_null_max")})
        table.append(row)
    normalized_values = [r["normalized_leading_constant"] for r in table]
    result = {
        "q": q, "radii": radii, "dps": dps, "drive": drive_path, "root": raw["root"],
        "dominant_characters": [list(c) for c in chars],
        "dominant_s": next(iter(s.values())), "dominant_rho": next(iter(rho.values())),
        "dominant_ratio_per_two_radius": dominant_rate,
        "normalization": "area_R = sum_c sector_areaSum(c,R)/(4q)^2; K_R = area_R / dominant_ratio^(R/2), where dominant_ratio is per R->R+2",
        "table": table,
        "normalized_min": min(normalized_values), "normalized_max": max(normalized_values),
        "normalized_R18_to_R40_relative_change": normalized_values[-1] / normalized_values[0] - 1,
        "records": [records[(R, c)] | {"R": R} for R in radii for c in chars],
        "seconds": time.time() - start,
        "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "qualification": "Direct non-interval high-precision numerical evidence. The algebraic rate is a candidate checked independently at every radius, not a proved recurrence or a Lean/cofinal certificate. Dominant characters suffice only for the leading normalized limit; subleading channels are not included in area_R."
    }
    Path(out_path).write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print("OUTPUT", out_path, "seconds", result["seconds"])
    for row in table:
        print("RATE", q, row["R"], mp.nstr(row["normalized_leading_constant"], 24),
              "max_ratio_error", mp.nstr(max((abs(c["ratio_relative_error"]) for c in row["per_character"]
                                               if c["ratio_relative_error"] is not None), default=mp.mpf(0)), 6))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--radii", default="18,20,22,24,26,28,30,32,34,36,38,40")
    ap.add_argument("--dps", type=int, default=70)
    ap.add_argument("--drive", required=True)
    ap.add_argument("--reuse", action="append", default=[])
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    run(a.q, [int(x) for x in a.radii.split(",")], a.dps, a.drive, a.reuse, a.out)
