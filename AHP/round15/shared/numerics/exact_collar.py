#!/usr/bin/env python3
"""Extract an exact cyclotomic dictionary for the frozen flat right collar.

The 12-component deep-collar blocks and the exceptional augmented-system rows
are written with exact coefficients in Q(zeta_{4q}).  Optional crossing-drive
solves supply separate non-interval residuals.  No Lean claim is made.
"""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "AHP/round6/probe"))
from probe import Family, Refine, mp, conj
sys.path.insert(0, str(ROOT / "AHP/round14/assembly/r2"))
from right_star import geometry
sys.path.insert(0, str(ROOT / "AHP/round15/shared/numerics"))
from cyclotomic import Cyc, identify, mat_zero, mat_mul, mat_sub, mat_inverse, mat_det
import argparse
import json
import resource
import time
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
CELLS = [(0, 0), (1, 0), (0, 1), (1, 1)]
ORDER = [(a, d) for d in range(3) for a in range(4)]


def mpc_string(s):
    p = s.strip().strip("()").split()
    if len(p) == 2:
        return mp.mpc(mp.mpf(p[0]), mp.mpf(p[1][:-1]))
    if len(p) == 3:
        return mp.mpc(mp.mpf(p[0]), mp.mpf(p[1] + p[2][:-1]))
    raise ValueError(s)


def exact_matrix(f, N, x, dx, dps):
    def var(xx, y, z, d):
        return f.em.get(f.bi[((xx, y, z), d)])
    out = mat_zero(N, 12)
    for row, (a, d) in enumerate(ORDER):
        ya, za = CELLS[a]
        for col, (b, e) in enumerate(ORDER):
            yb, zb = CELLS[b]
            i, j = var(x, ya, za, d), var(x + dx, yb, zb, e)
            if i is not None and j is not None:
                out[row][col] = identify(f.K.r[i].get(j, 0), N, dps)
    return out


def descriptors(f):
    ans = []
    for i in range(f.n):
        x, d = f.bonds[f.e[i]]
        ans.append({"index": i, "kind": "bond", "x": x[0], "y": x[1], "z": x[2], "direction": d})
    for i in range(f.n, f.aug.n):
        k = i - f.n
        block = 0 if k < f.H.n else 1
        site_index = k if block == 0 else k - f.H.n
        x = f.sites[site_index]
        ans.append({"index": i, "kind": "multiplier", "x": x[0], "y": x[1], "z": x[2], "block": block})
    return ans


def run(q, R, iy, iz, x, dps, drive_path=None):
    mp.mp.dps = dps
    start = time.time()
    N = 4 * q
    f = Family(q, R, mp.mpf(0), iy, iz, 1).assemble()
    out, _ = f.plaq("out", 0)
    for i, row in enumerate(out.r):
        if i in f.em:
            for j, v in row.items():
                if j in f.em:
                    f.aug.put(f.em[i], f.em[j], v)
    A, B, C = (exact_matrix(f, N, x, dx, dps) for dx in (1, 0, -1))
    # Direction zero is eliminated exactly, leaving eight transverse components.
    A00, A01 = [row[:4] for row in A[:4]], [row[4:] for row in A[:4]]
    A10, A11 = [row[:4] for row in A[4:]], [row[4:] for row in A[4:]]
    B00, B01 = [row[:4] for row in B[:4]], [row[4:] for row in B[:4]]
    B10, B11 = [row[:4] for row in B[4:]], [row[4:] for row in B[4:]]
    C00, C01 = [row[:4] for row in C[:4]], [row[4:] for row in C[:4]]
    C10, C11 = [row[:4] for row in C[4:]], [row[4:] for row in C[4:]]
    if not all(not z for row in A00 + C00 for z in row):
        raise AssertionError(("A00/C00", [[z.expression() for z in row] for row in A00],
                              [[z.expression() for z in row] for row in C00]))
    if not all(not z for row in A10 + C01 for z in row):
        raise AssertionError(("A10/C01", [[z.expression() for z in row] for row in A10],
                              [[z.expression() for z in row] for row in C01]))
    B00inv = mat_inverse(B00)
    ar = mat_sub(A11, mat_mul(mat_mul(B10, B00inv), A01))
    br = mat_sub(mat_sub(B11, mat_mul(mat_mul(B10, B00inv), B01)),
                 mat_mul(mat_mul(C10, B00inv), A01))
    cr = mat_sub(C11, mat_mul(mat_mul(C10, B00inv), B01))
    det_a, det_c = mat_det(ar), mat_det(cr)
    # Constant-row checks use exact arithmetic, not a fit.
    deep = f.s + 5
    comparisons = []
    for xx in [f.s - 2, f.s - 1, f.s, f.s + 1, f.s + 2, deep, f.hi - 2, f.hi - 1]:
        if xx < f.s or xx > f.hi - 1:
            continue
        mats = [exact_matrix(f, N, xx, dx, dps) for dx in (1, 0, -1)]
        refs = [exact_matrix(f, N, deep, dx, dps) for dx in (1, 0, -1)]
        differences = []
        for M, D in zip(mats, refs):
            diff = mat_sub(M, D)
            differences.append(max((abs(z.numeric(dps)) for row in diff for z in row), default=mp.mpf(0)))
        comparisons.append({"x": xx, "Kplus_deep_difference": differences[0],
                            "K0_deep_difference": differences[1],
                            "Kminus_deep_difference": differences[2]})
    desc = descriptors(f)
    interface_rows = []
    for i in range(f.aug.n):
        xx = desc[i]["x"]
        if not (f.s - 4 <= xx <= f.s or xx == f.hi - 1):
            continue
        entries = []
        for j, v in f.aug.r[i].items():
            entries.append({"col": j, "col_x": desc[j]["x"], "value": identify(v, N, dps).json()})
        interface_rows.append({"row": i, "descriptor": desc[i], "entries": entries})
    # Optional non-interval solve and residuals for the actual augmented vector.
    solve_data = None
    if drive_path:
        raw = json.loads(Path(drive_path).read_text())
        drive = [mpc_string(s) for s in raw["z"]]
        boundary = q * (12 * R + 12)
        _, bonds = geometry(boundary, "right")
        phis = [f.index(*b) for b in bonds]
        solver = Refine(f.aug)
        Y = [mp.mpc(0)] * f.aug.n
        rhs_total = [mp.mpc(0)] * f.aug.n
        residual = mp.mpf(0)
        for col, (j, phase) in enumerate(phis):
            rhs = [0] * f.aug.n
            rhs[f.em[j]] = conj(phase)
            sol = solver.solve(rhs)
            residual = max(residual, max(abs(a - b) for a, b in zip(f.aug.apply(sol), rhs)))
            for k in range(f.aug.n):
                Y[k] += drive[col] * sol[k]
                rhs_total[k] += drive[col] * rhs[k]
        ay = f.aug.apply(Y)
        rows = []
        for i in range(f.aug.n):
            xx = desc[i]["x"]
            if xx < f.s - 4 or xx >= f.hi:
                continue
            ar = abs(ay[i] - rhs_total[i])
            scale = max(abs(ay[i]), abs(rhs_total[i]),
                        max((abs(v * Y[j]) for j, v in f.aug.r[i].items()), default=mp.mpf(0)))
            rows.append({"row": i, "x": xx, "absolute_residual": ar,
                         "relative_residual": ar / max(scale, mp.power(10, -dps + 4)),
                         "rhs": rhs_total[i], "AY": ay[i]})
        solve_data = {"drive": str(drive_path), "root": raw["root"],
                      "flat_resolvent_absolute_residual": residual,
                      "max_row_relative_residual": max((r["relative_residual"] for r in rows), default=mp.mpf(0)),
                      "rows": rows}
    result = {
        "q": q, "R": R, "character": [iy, iz], "x": x, "s": f.s, "hi": f.hi, "dps": dps,
        "field": f"Q(zeta_{N}), zeta_{N}=exp(2*pi*i/{N}), zeta_{N}^{N//2}=-1",
        "cells": CELLS, "order": ORDER,
        "deep_recurrence": "K_- v_(x-1)+K_0 v_x+K_+ v_(x+1)=0; constant for s+1<=x<=hi-2",
        "blocks": {str(dx): M for dx, M in zip((-2, -1, 0, 1, 2),
                    [exact_matrix(f, N, x, dx, dps) for dx in (-2, -1, 0, 1, 2)])},
        "reduced_blocks": {"A": ar, "B": br, "C": cr},
        "reduced_determinants": {"A": det_a, "C": det_c},
        "constant_row_comparisons": comparisons,
        "interface_rows": interface_rows,
        "descriptors": desc,
        "solve": solve_data,
        "seconds": time.time() - start,
        "qualification": "Exact sparse cyclotomic transcription of the numerical frozen-family operator; residuals are non-interval numerical evidence. No Lean identification or area-seed proof is asserted."
    }
    return result


def jsonable(x):
    if isinstance(x, Cyc):
        return x.json()
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp.nstr(x, mp.mp.dps - 5)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--R", type=int, required=True)
    ap.add_argument("--iy", type=int, required=True)
    ap.add_argument("--iz", type=int, required=True)
    ap.add_argument("--x", type=int, default=None)
    ap.add_argument("--dps", type=int, default=70)
    ap.add_argument("--drive")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    result = run(a.q, a.R, a.iy, a.iz,
                 a.x if a.x is not None else a.q * (10 * a.R + 12) + 5,
                 a.dps, a.drive)
    target = Path(a.out)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(jsonable(result), indent=2) + "\n")
    print("OUTPUT", target, "seconds", result["seconds"])
