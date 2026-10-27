#!/usr/bin/env python3
"""Set-level evidence for the s2 inclusion geometry. Not a proof and not a theorem.

Every predicate below is a direct transcription of a Lean definition. The script
does not model Delta, J, genForm, or any gauge field. It does not decide
IsClassCube: that also needs GridCorner, the two-stratum clause and uniqueness
(ZStatementP428.lean:131-143). Results are counts on tori of side at most 8.

Citations
- periodicLatticeShift: lean/src/AdalyFormal/Target/ClayStatement.lean:1281
  Function.update x μ (x μ + 1), one step mod (L μ + 1).
- periodicPlaquetteBoundaryEdges: ClayStatement.lean:1295
  {(x, μ), (shift x μ, ν), (shift x ν, μ), (x, ν)} with μ < ν.
- siteBox: lean/src/ZStatementP428.lean:122
  (x_μ + N_μ - z_μ) mod N_μ < s, N_μ = L μ + 1.
- CubeBond: ZStatementP428.lean:145, both endpoints.
- TouchBond: AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean, one endpoint.
  Same formula as CubeBond with ∧ replaced by ∨.
- plaqIn: lean/src/ZR2Ops2.lean:74, CubeBond on all four boundary bonds.
- plaqCorner: one of the four corners, ClassInclusion.lean (S1Touching.plaqCorner).
- CoversPlaqOm0c antecedent: ZR6A.lean:27, the plaqIn side.
- CoversPlaqFour antecedent: all four bonds TouchBond.
- bigSide: ZStatementP428.lean:51, M * ell^j. Not used numerically; the script
  checks site boxes, not the factor-c class cubes built from bigSide.
"""

from __future__ import annotations

import json
import time

import numpy as np

PAIRS = ((0, 1), (0, 2), (1, 2))


def plaquettes(n: int):
    """All unit plaquettes. corners: (P, 4, 3) in order A, B, C, D."""
    xs = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    bases = np.repeat(xs, 3, axis=0)
    dirs = np.tile(np.array(PAIRS, dtype=np.int16), (xs.shape[0], 1))
    idx = np.arange(bases.shape[0])
    A = bases.copy()
    B = bases.copy()
    B[idx, dirs[:, 0]] = (B[idx, dirs[:, 0]] + 1) % n
    C = bases.copy()
    C[idx, dirs[:, 1]] = (C[idx, dirs[:, 1]] + 1) % n
    D_from_B = B.copy()
    D_from_B[idx, dirs[:, 1]] = (D_from_B[idx, dirs[:, 1]] + 1) % n
    D_from_C = C.copy()
    D_from_C[idx, dirs[:, 0]] = (D_from_C[idx, dirs[:, 0]] + 1) % n
    if not np.array_equal(D_from_B, D_from_C):
        raise RuntimeError("shift_comm failed: ClayStatement shift vs ZR8Class.lean:87")
    corners = np.stack([A, B, C, D_from_B], axis=1)
    return corners


def in_sitebox(points: np.ndarray, z: np.ndarray, s: int, n: int) -> np.ndarray:
    """points (..., 3) -> bool (...). ZStatementP428.lean:122."""
    off = (points.astype(np.int16) - z.astype(np.int16)) % n
    return np.all(off < s, axis=-1)


def classify(corners: np.ndarray, inside: np.ndarray):
    """inside (P, 4) corner membership. Returns masks."""
    A, B, C, D = (inside[:, i] for i in range(4))
    # TouchBond on the four Lean edges AB, BD, CD, AC.
    touch = (A | B) & (B | D) & (C | D) & (A | C)
    cube = A & B & C & D
    corner = A | B | C | D
    return touch, cube, corner


def geometry_scan(n: int) -> dict:
    """For every siteBox and every plaquette: touch-cover implies all four corners in."""
    corners = plaquettes(n)
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    fails = 0
    touch_hits = 0
    cube_hits = 0
    # Antecedent direction: cube-cover implies touch-cover. Expect 0 failures.
    ante_fails = 0
    t0 = time.perf_counter()
    for s in range(0, n + 1):
        for z in sites:
            inside = in_sitebox(corners, z, s, n)
            touch, cube, _ = classify(corners, inside)
            touch_hits += int(touch.sum())
            cube_hits += int(cube.sum())
            fails += int(np.count_nonzero(touch & ~cube))
            ante_fails += int(np.count_nonzero(cube & ~touch))
    return {
        "n": n,
        "plaquettes": int(corners.shape[0]),
        "boxes": int(sites.shape[0] * (n + 1)),
        "touch_cover_instances": touch_hits,
        "cube_cover_instances": cube_hits,
        "touch_without_cube": fails,
        "cube_without_touch": ante_fails,
        "seconds": round(time.perf_counter() - t0, 3),
    }


def domain_report(n: int, member, label: str, focus=None) -> dict:
    """Set-level plaquette counts for one site set. Not an admissible tower."""
    corners = plaquettes(n)
    inside = member(corners.reshape(-1, 3)).reshape(corners.shape[0], 4)
    touch, cube, corner = classify(corners, inside)
    out = {
        "label": label,
        "n": n,
        "sites": int(np.count_nonzero(member(np.indices((n, n, n)).reshape(3, -1).T))),
        "plaqCorner": int(corner.sum()),
        "fourTouch": int(touch.sum()),
        "plaqIn": int(cube.sum()),
        "fourTouch_not_plaqIn": int(np.count_nonzero(touch & ~cube)),
        "plaqIn_not_fourTouch": int(np.count_nonzero(cube & ~touch)),
        "corner_not_fourTouch": int(np.count_nonzero(corner & ~touch)),
    }
    if focus is not None:
        out["focus"] = focus
    return out


def product_block(n: int, s: int):
    def member(pts):
        return in_sitebox(pts, np.zeros(3, dtype=np.int16), s, n)

    return member


def l_shape(n: int):
    """Two side-2 blocks meeting only diagonally: [0,2)^3 and [2,4)x[2,4)x[0,2)."""

    def member(pts):
        x, y, z = pts[..., 0], pts[..., 1], pts[..., 2]
        b1 = (x < 2) & (y < 2) & (z < 2)
        b2 = (x >= 2) & (x < 4) & (y >= 2) & (y < 4) & (z < 2)
        return b1 | b2

    return member


def bond_counts(n: int, s: int) -> dict:
    """CubeBond vs TouchBond edges of siteBox(0, s). Directions are the three axes.
    An edge is a pair (site, μ), ClayStatement PeriodicLatticeEdge."""
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    inside = in_sitebox(sites, np.zeros(3, dtype=np.int16), s, n)
    inside_grid = inside.reshape(n, n, n)
    cube = 0
    touch = 0
    for mu in range(3):
        shifted = np.roll(inside_grid, -1, axis=mu)
        cube += int(np.count_nonzero(inside_grid & shifted))
        touch += int(np.count_nonzero(inside_grid | shifted))
    return {
        "n": n,
        "s": s,
        "sites_in_box": int(inside.sum()),
        "cubeBonds": cube,
        "touchBonds": touch,
        "extra_touch_bonds": touch - cube,
    }


def boxes_subset_covering(n: int, member, plaquette_corners_row) -> dict:
    """How many siteBoxes contained in `member` touch-cover this one plaquette.
    Touch-cover uses the four edge disjunctions, i.e. TouchBond of the box."""
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    grid = member(sites).reshape(n, n, n)
    row = plaquette_corners_row.astype(np.int16)
    hits = 0
    subsets = 0
    for s in range(1, n + 1):
        for z in sites:
            # box sites
            ranges = [(int(z[mu]) + np.arange(s)) % n for mu in range(3)]
            mesh = np.stack(np.meshgrid(*ranges, indexing="ij"), -1).reshape(-1, 3)
            if not np.all(grid[mesh[:, 0], mesh[:, 1], mesh[:, 2]]):
                continue
            subsets += 1
            inside = in_sitebox(row, z, s, n)
            A, B, C, D = (bool(inside[i]) for i in range(4))
            if (A or B) and (B or D) and (C or D) and (A or C):
                hits += 1
    return {"subset_boxes": subsets, "subset_boxes_touch_covering_focus": hits}


def main():
    t0 = time.perf_counter()
    scans = [geometry_scan(n) for n in (2, 4, 6, 8)]
    if any(s["touch_without_cube"] or s["cube_without_touch"] for s in scans):
        raise RuntimeError(f"geometry scan failed: {scans}")

    n = 8
    corners = plaquettes(n)
    # Hand plaquette on the product block: base (3,0,0), μ=0<ν=1.
    # A in, B out, C in, D out. Bond BD has both endpoints out.
    prod = product_block(n, 4)
    # Find that plaquette: A=(3,0,0), B=(4,0,0), C=(3,1,0), D=(4,1,0).
    target = np.array([[3, 0, 0], [4, 0, 0], [3, 1, 0], [4, 1, 0]], dtype=np.int16)
    match = np.where(np.all(corners == target, axis=(1, 2)))[0]
    if match.size != 1:
        raise RuntimeError(f"exit plaquette not unique: {match.size}")
    i = int(match[0])
    pinside = prod(corners[i])
    exit_plaq = {
        "corners_ABCD": target.tolist(),
        "in_product_block_side4": [bool(x) for x in pinside],
        "fourTouch": bool((pinside[0] or pinside[1]) and (pinside[1] or pinside[3])
                          and (pinside[2] or pinside[3]) and (pinside[0] or pinside[2])),
        "plaqIn": bool(pinside.all()),
        "plaqCorner": bool(pinside.any()),
        "bond_BD_both_out": bool((not pinside[1]) and (not pinside[3])),
    }
    prod_rep = domain_report(n, prod, "product siteBox origin side 4 on side-8 torus", exit_plaq)

    # Diagonal plaquette on the L: A=(1,1,0), B=(2,1,0), C=(1,2,0), D=(2,2,0).
    ell = l_shape(n)
    diag = np.array([[1, 1, 0], [2, 1, 0], [1, 2, 0], [2, 2, 0]], dtype=np.int16)
    match = np.where(np.all(corners == diag, axis=(1, 2)))[0]
    if match.size != 1:
        raise RuntimeError(f"diagonal plaquette not unique: {match.size}")
    j = int(match[0])
    linside = ell(corners[j])
    cover = boxes_subset_covering(n, ell, corners[j])
    diag_plaq = {
        "corners_ABCD": diag.tolist(),
        "in_L": [bool(x) for x in linside],
        "fourTouch": bool((linside[0] or linside[1]) and (linside[1] or linside[3])
                          and (linside[2] or linside[3]) and (linside[0] or linside[2])),
        "plaqIn": bool(linside.all()),
        "plaqCorner": bool(linside.any()),
        **cover,
    }
    ell_rep = domain_report(n, ell, "L of two side-2 blocks on side-8 torus", diag_plaq)

    # Same exit plaquette: no siteBox contained in the product block touch-covers it,
    # because B and D are outside every such box. Recorded as a count.
    exit_cover = boxes_subset_covering(n, prod, corners[i])

    out = {
        "note": (
            "Numerical evidence only. Zero touch-without-cube counts support the "
            "product-box step used by CoversPlaqFour.toFrozen. They are not a Lean "
            "check and not a proof. Domain counts are set-level; they do not inhabit "
            "IsClassCube, Admissible, or PerCubeRegularTouch."
        ),
        "geometry_scans": scans,
        "product_block": prod_rep,
        "exit_plaq_subset_boxes": exit_cover,
        "l_shape": ell_rep,
        "bond_counts_product_side4": bond_counts(n, 4),
        "seconds_total": round(time.perf_counter() - t0, 3),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
