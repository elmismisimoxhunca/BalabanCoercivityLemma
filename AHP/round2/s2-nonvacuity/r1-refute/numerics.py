#!/usr/bin/env python3
"""Exact finite geometry exploration; evidence, not headline instances.

Transcription anchors (file and declaration line):
* lean/src/AdalyFormal/Target/ClayStatement.lean:1281 periodicLatticeShift
* same file:1295 periodicPlaquetteBoundaryEdges (AB, BD, CD, AC)
* lean/src/ZStatementP428.lean:122 siteBox
* AHP/round2/s2-nonvacuity/pin/Statement.lean:41 TouchBond
* same file:44 CoversPlaqFour (antecedent only)
* same file:49 plaqCorner; :54 CoversPlaqCorner (necessary box coverage only)
No gauge operator, Admissible, GridCorner, or class factor is simulated.
Every class cube is a siteBox, so searching all contained siteBoxes relaxes
its witness requirement. Saturation in these small scans is not a proof.
"""
from itertools import product, combinations
import json
import resource

resource.setrlimit(resource.RLIMIT_AS, (3_500_000_000, 3_500_000_000))


def shift(x, mu, n):
    return tuple((v + (i == mu)) % n for i, v in enumerate(x))


def corners(x, mu, nu, n):
    b = shift(x, mu, n)
    return (x, b, shift(x, nu, n), shift(b, nu, n))


def touch_all(q, domain):
    a, b, c, d = (x in domain for x in q)
    return (a or b) and (b or d) and (c or d) and (a or c)


def boxes(n):
    pts = list(product(range(n), repeat=3))
    for z in pts:
        for s in range(n + 1):
            yield frozenset(x for x in pts if all((x[i] - z[i]) % n < s for i in range(3)))


def exhaustive_side2():
    n = 2
    pts = list(product(range(n), repeat=3))
    qs = [corners(x, mu, nu, n) for x in pts for mu, nu in combinations(range(3), 2)]
    bs = list(set(boxes(n)))
    passes = []
    for bits in range(1, 255):
        domain = {x for i, x in enumerate(pts) if bits >> i & 1}
        contained = [b for b in bs if b <= domain]
        if all(any(touch_all(q, b) for b in contained)
               for q in qs if any(x in domain for x in q)):
            passes.append(bits)
    assert not passes
    return {"proper_domains_tested": 254, "corner_coverage_passes": len(passes)}


def boundary_candidate(n):
    # A proper product block and its explicit exit plaquette.
    width = n // 2
    domain = {x for x in product(range(n), repeat=3) if all(v < width for v in x)}
    q = corners((width - 1, 0, 0), 0, 1, n)
    contained = [b for b in boxes(n) if b and b <= domain]
    covering = sum(touch_all(q, b) for b in contained)
    assert any(x in domain for x in q) and not touch_all(q, domain) and covering == 0
    return {"side": n, "width": width, "corners_ABCD": q,
            "corner_membership": [x in domain for x in q],
            "four_antecedent": touch_all(q, domain),
            "contained_nonempty_boxes": len(contained), "covering_boxes": covering}


print(json.dumps({"scope": "geometry only; no headline witness claimed",
                  "exhaustive": exhaustive_side2(),
                  "candidates": [boundary_candidate(n) for n in (4, 5, 8)]}, indent=2))
