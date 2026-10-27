#!/usr/bin/env python3
"""Kimi attack checks for s2-inclusion. Evidence only, not a proof and not a theorem.

Three independent checks against AHP/fidelity/s2-inclusion (SPEC.md,
numerics/inclusion_geometry.py, lean/ClassInclusion.lean):

1. PARITY GAP. inclusion_geometry.py scans only even sides 2,4,6,8, but the
   print's blocking factor L is odd > 11 (OPEN_ITEMS S-4) and the Lean lemmas
   quantify over every PeriodicLatticeExtent. Re-run the same scan on sides
   1, 3, 5, 7 (side 1 included: degenerate plaquettes, boundary finset has 2
   edges; the Lean lemmas are stated for all L).
   Same transcriptions as inclusion_geometry.py: periodicLatticeShift
   (ClayStatement.lean:1281), periodicPlaquetteBoundaryEdges (:1295), siteBox
   (ZStatementP428.lean:122), CubeBond (:145).

2. CORNER-CLASS SATURATION. The s2 variant keeps CoversPlaqCorner (same text
   as S1Touching, which drafts saturated_of_coversCorner, uncompiled). A class
   cube is a siteBox contained in two strata (DescribedAt,
   ZStatementP428.lean:131-137; towerBj = Om j \\ Om (j+1), :118-119), hence in
   Om_0 under Admissible. Set/box-level check: on every proper nonempty subset
   of the side-2 torus (254 of them, exhaustive) and on structured/random
   subsets of the side-3 torus, some one-corner plaquette is touch-covered by
   NO siteBox contained in the subset. If so, CoversPlaqCorner fails on every
   tested proper nonempty Om_0.

3. FOUR-CLASS ANTECEDENT ON PRODUCT BOXES. On a product-box domain the
   four-touch antecedent of CoversPlaqFour collapses to plaqIn (consequence of
   touchCover_all_corners). Verify fourTouch == plaqIn for every siteBox as
   domain on sides 2,3,4,5. This is the route by which ClassCoupledFour could
   admit a proper nonempty Om_0; full inhabitation (Admissible, IsClassCube
   with factor 12, PerCubeRegularTouch) is NOT decided here.

No gauge-field operator is modelled. All counts are exact integers.
"""

from __future__ import annotations

import itertools
import json
import time

import numpy as np

PAIRS = ((0, 1), (0, 2), (1, 2))


def plaquettes(n: int):
    """corners (P, 4, 3) in order A, B, C, D; edges AB, BD, CD, AC as in
    ClayStatement.lean:1295 {(x,mu),(shift x mu,nu),(shift x nu,mu),(x,nu)}."""
    xs = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    bases = np.repeat(xs, 3, axis=0)
    dirs = np.tile(np.array(PAIRS, dtype=np.int16), (xs.shape[0], 1))
    idx = np.arange(bases.shape[0])
    A = bases.copy()
    B = bases.copy(); B[idx, dirs[:, 0]] = (B[idx, dirs[:, 0]] + 1) % n
    C = bases.copy(); C[idx, dirs[:, 1]] = (C[idx, dirs[:, 1]] + 1) % n
    D = B.copy(); D[idx, dirs[:, 1]] = (D[idx, dirs[:, 1]] + 1) % n
    return np.stack([A, B, C, D], axis=1)


def in_sitebox(points: np.ndarray, z: np.ndarray, s: int, n: int) -> np.ndarray:
    """ZStatementP428.lean:122."""
    off = (points.astype(np.int16) - z.astype(np.int16)) % n
    return np.all(off < s, axis=-1)


def classify(corners: np.ndarray, inside: np.ndarray):
    A, B, C, D = (inside[:, i] for i in range(4))
    touch = (A | B) & (B | D) & (C | D) & (A | C)  # TouchBond on AB, BD, CD, AC
    cube = A & B & C & D                            # CubeBond on all four edges
    corner = A | B | C | D                          # plaqCorner
    return touch, cube, corner


def geometry_scan(n: int) -> dict:
    corners = plaquettes(n)
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    fails = ante = 0
    for s in range(0, n + 1):
        for z in sites:
            inside = in_sitebox(corners, z, s, n)
            touch, cube, _ = classify(corners, inside)
            fails += int(np.count_nonzero(touch & ~cube))
            ante += int(np.count_nonzero(cube & ~touch))
    return {"n": n, "touch_without_cube": fails, "cube_without_touch": ante}


def all_boxes(n: int, proper_only: bool = False):
    """Yield (mask (n^3 bool), z, s) for every siteBox. s = 0 skipped."""
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    lo = 1
    hi = n if proper_only else n + 1  # s = n is the whole torus
    for s in range(lo, hi):
        for z in sites:
            mask = in_sitebox(sites, z, s, n)
            yield mask, z, s


def corner_saturation_check(n: int, masks, label: str) -> dict:
    """For each subset mask: does some plaqCorner plaquette admit no touch-cover
    by a siteBox contained in the subset?"""
    corners = plaquettes(n)
    P = corners.shape[0]
    sites = np.indices((n, n, n)).reshape(3, -1).T.astype(np.int16)
    boxes = []
    for mask, z, s in all_boxes(n, proper_only=True):
        boxes.append((mask, in_sitebox(corners, z, s, n)))
    tested = failed = 0
    uncoverable_total = 0
    examples = []
    for mask in masks:
        cnt = int(mask.sum())
        if cnt == 0 or cnt == n ** 3:
            continue
        tested += 1
        inside = mask[corners[:, :, 0] * n * n + corners[:, :, 1] * n + corners[:, :, 2]]
        _, cube, corner = classify(corners, inside)
        # witness: a corner plaquette that is not plaqIn
        witness_idx = np.where(corner & ~cube)[0]
        bad = 0
        first_uncoverable = None
        for i in range(P):
            if not corner[i]:
                continue
            covered = False
            for bmask, bcorners in boxes:
                if not np.all(bmask <= mask):
                    continue  # box not contained in the subset
                A, B, C, D = (bool(bcorners[i, k]) for k in range(4))
                if (A or B) and (B or D) and (C or D) and (A or C):
                    covered = True
                    break
            if not covered:
                bad += 1
                if first_uncoverable is None:
                    first_uncoverable = corners[i].tolist()
        uncoverable_total += bad
        if bad == 0:
            failed += 1
            examples.append({"mask_nonzero": cnt})
        elif len(examples) < 2 and witness_idx.size:
            pass
    return {
        "label": label,
        "n": n,
        "proper_nonempty_subsets_tested": tested,
        "subsets_where_every_corner_plaq_coverable": failed,
        "uncoverable_corner_plaquettes_total": uncoverable_total,
        "fail_examples": examples,
    }


def side2_all_masks():
    n = 2
    sites = np.indices((n, n, n)).reshape(3, -1).T
    for bits in range(1, 2 ** 8 - 1):
        mask = np.array([(bits >> i) & 1 == 1 for i in range(8)])
        yield mask


def side3_sample_masks():
    n = 3
    rng = np.random.default_rng(20261020)
    # all 1-site sets and their complements
    for i in range(27):
        m = np.zeros(27, dtype=bool); m[i] = True
        yield m
        yield ~m
    # all proper product boxes and their complements
    for mask, z, s in all_boxes(3, proper_only=True):
        if 0 < mask.sum() < 27:
            yield mask
            yield ~mask
    # random masks
    for _ in range(300):
        k = int(rng.integers(1, 27))
        m = np.zeros(27, dtype=bool)
        m[rng.choice(27, size=k, replace=False)] = True
        yield m


def product_box_antecedent(n: int) -> dict:
    """fourTouch == plaqIn for every siteBox taken as the domain."""
    corners = plaquettes(n)
    mismatches = 0
    boxes = 0
    for mask, z, s in all_boxes(n):
        inside = in_sitebox(corners, z, s, n)
        touch, cube, _ = classify(corners, inside)
        boxes += 1
        mismatches += int(np.count_nonzero(touch != cube))
    return {"n": n, "boxes": boxes, "fourTouch_neq_plaqIn": mismatches}


def main():
    t0 = time.perf_counter()
    odd_scans = [geometry_scan(n) for n in (1, 3, 5, 7)]
    sat2 = corner_saturation_check(2, side2_all_masks(), "exhaustive side 2")
    sat3 = corner_saturation_check(3, side3_sample_masks(), "structured+random side 3")
    boxeq = [product_box_antecedent(n) for n in (2, 3, 4, 5)]
    out = {
        "note": "Kimi attack evidence. Not a proof. Set/box level only.",
        "odd_and_degenerate_geometry_scans": odd_scans,
        "corner_saturation": [sat2, sat3],
        "product_box_antecedent_equivalence": boxeq,
        "seconds_total": round(time.perf_counter() - t0, 3),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
