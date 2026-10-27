#!/usr/bin/env python3
"""S-1 refutation search. Evidence only; not InstIneqS or class certification.

Frozen operators modelled (paths relative to lean/src/):
  AdalyFormal/Target/ClayStatement.lean:1281 periodicLatticeShift,
    :1286 periodicPlaquetteHolonomy, :1295 periodicPlaquetteBoundaryEdges;
  ZStatementP428.lean:54 BlockClosed, :122 siteBox;
  ZR2Ops2.lean:74 plaqIn;
  ZR2A.lean:29 curlA, :40 ddA, :48 PerCubeRegular2;
  D1Path.lean:25 Zb, :46 Uth;
  AdalyFormal/Balaban/CovariantOperators.lean:315 curlValueCovariant,
    :247 RMap (identity on the diagonal Cartan sector);
  AdalyFormal/Balaban/SuTwoInner.lean:104 hsInner (Cartan unit has norm one);
  D1Eval.lean:56 delta_form_sum, specialised to diagonal links and test fields:
    sum_p cos(phi_p) curl(B)_p^2, phi=theta0+theta1-theta2-theta3;
  D1Geo1.lean:94 BdPt.delta_pi (anchor: outward unit bond gives -4 at pi).
Pinned selectors/guards:
  AHP/round2/s1-touching/pin/Statement.lean:33 plaqCorner, :30 TouchBond,
    :45 CoversPlaqCorner, :55 PerCubeRegularTouch, :142 ReadBond.

The finite geometry experiment RELAXES class cubes to every product box of any
side contained in Omega, ignoring factor/alignment/strata. Failure of this larger
coverage search is an obstruction, never an admissible-tower certificate.
The phase experiment globally bounds all three regularity expressions at j=k=2
in the identity gauge, a sufficient numerical regularity check for any cube of
index <=2 at cap 12*M*alpha=a0. Geometry, Lambda and headline thresholds are NOT
certified. No Q, J, W, inverse or full genForm is numerically substituted.
"""
import resource
resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
import itertools
import json
from pathlib import Path
import numpy as np


def shift(x, mu, n):
    y = list(x)
    y[mu] = (y[mu] + 1) % n
    return tuple(y)


def sites(n):
    return list(itertools.product(range(n), repeat=3))


def plaquettes(n):
    return [(x, a, b) for x in sites(n) for a, b in ((0, 1), (0, 2), (1, 2))]


def corners(p, n):
    x, a, b = p
    return (x, shift(x, a, n), shift(x, b, n), shift(shift(x, a, n), b, n))


def edges(p, n):
    x, a, b = p
    return ((x, a), (shift(x, a, n), b), (shift(x, b, n), a), (x, b))


def finite_coverage():
    n = 4
    xs = sites(n)
    ps = plaquettes(n)
    index = {x: i for i, x in enumerate(xs)}
    bits = lambda ss: sum(1 << index[x] for x in set(ss))
    corner_masks = [bits(corners(p, n)) for p in ps]
    boxes = []
    tested_box_plaquette_pairs = 0
    for z in xs:
        for side in range(1, n + 1):
            box = {x for x in xs if all((x[a] - z[a]) % n < side for a in range(3))}
            bmask = bits(box)
            covered = 0
            for i, p in enumerate(ps):
                ht = all(x in box or shift(x, a, n) in box for x, a in edges(p, n))
                if ht:
                    assert all(x in box for x in corners(p, n))
                    covered |= 1 << i
                tested_box_plaquette_pairs += 1
            boxes.append((bmask, covered))
    blocks = [bits(x for x in xs if tuple(v // 2 for v in x) == b)
              for b in itertools.product(range(2), repeat=3)]
    passing = []
    for subset in range(256):
        omega = sum(blocks[i] for i in range(8) if subset & (1 << i))
        wanted = sum(1 << i for i, cm in enumerate(corner_masks) if cm & omega)
        available = 0
        for bm, pc in boxes:
            if bm & ~omega == 0:
                available |= pc
        if wanted & ~available == 0:
            passing.append(subset)
    assert passing == [0, 255]
    return {"N": n, "M": 2, "block_domains_tested": 256,
            "relaxed_boxes_per_domain": len(boxes),
            "box_plaquette_pairs_checked": tested_box_plaquette_pairs,
            "passing_block_masks": passing, "proper_nonempty_passes": 0}


def hidden_bond_scan(n, width):
    xs = sites(n)
    omega = {x for x in xs if x[0] < width}
    ps = [p for p in plaquettes(n) if any(x in omega for x in corners(p, n))]
    read = set(e for p in ps for e in edges(p, n))
    far = {(x, a) for x in xs for a in range(3)
           if x not in omega and shift(x, a, n) not in omega}
    p = ((width - 1, 0, 0), 0, 1)
    invisible = (shift(p[0], 0, n), 1)
    assert invisible in far and invisible in read
    assert invisible in edges(p, n)
    target = ((width - 1, 0, 0), 0)
    rayleigh = []
    for theta in (0.0, 0.01, np.pi / 4, np.pi / 2, np.pi):
        q = 0.0
        for qplaq in ps:
            es = edges(qplaq, n)
            coeff = sum(sign for e, sign in zip(es, (1, 1, -1, -1)) if e == target)
            if coeff:
                phi = sum(sign * theta for e, sign in zip(es, (1, 1, -1, -1)) if e in far)
                q += np.cos(phi) * coeff**2
        assert abs(q - 4 * np.cos(theta)) < 1e-12
        rayleigh.append({"theta": float(theta), "raw_delta_unit_bond": float(q)})
    return {"N": n, "width": width, "corner_plaquettes": len(ps),
            "read_bonds_outside_touch": len(read & far),
            "uncoverable_plaquette": p, "opposite_bond_outside_Omega": invisible,
            "Uth_rayleigh": rayleigh,
            "primary_class": "fails corner coverage for every theta, regardless of regularity"}


def forward(t, a):
    return np.roll(t, -1, axis=a)


def curl(t, a, b):
    return forward(t[..., b], a) - t[..., b] - forward(t[..., a], b) + t[..., a]


def dd(t):
    out = np.zeros_like(t)
    for mu in range(3):
        for nu in range(3):
            if nu != mu:
                f = curl(t, nu, mu)
                out[..., mu] += np.roll(f, 1, axis=nu) - f
    return out


def raw_q(t, field, mask):
    return float(sum(np.sum(np.cos(curl(t, a, b)) * curl(field, a, b)**2 * mask[a, b])
                     for a, b in ((0, 1), (0, 2), (1, 2))))


def small_phase_search(n, a0, trials, rng):
    ell, k = 2, 2
    omega = np.indices((n, n, n))[0] < n // 2
    masks = {"all": {}, "corner": {}, "inside": {}}
    for a, b in ((0, 1), (0, 2), (1, 2)):
        cs = [omega, forward(omega, a), forward(omega, b), forward(forward(omega, a), b)]
        masks["all"][a, b] = np.ones_like(omega)
        masks["corner"][a, b] = np.logical_or.reduce(cs)
        masks["inside"][a, b] = np.logical_and.reduce(cs)
    min_cos, max_phase, max_ratio = 1.0, 0.0, 0.0
    min_q = {key: float("inf") for key in masks}
    eig_min = []
    for _ in range(trials):
        t = rng.uniform(-1.0, 1.0, size=(n, n, n, 3))
        boundnorm = max(ell**k * np.max(np.abs(t)),
                        ell**(2*k) * max(np.max(np.abs(forward(t, a) - t)) for a in range(3)),
                        ell**(3*k) * np.max(np.abs(dd(t))))
        t *= 0.9 * a0 / (np.sqrt(2) * boundnorm)
        ratio = np.sqrt(2) / a0 * max(ell**k * np.max(np.abs(t)),
                      ell**(2*k) * max(np.max(np.abs(forward(t, a) - t)) for a in range(3)),
                      ell**(3*k) * np.max(np.abs(dd(t))))
        assert ratio < 1
        max_ratio = max(max_ratio, float(ratio))
        max_phase = max(max_phase, float(np.max(np.abs(t))))
        min_cos = min(min_cos, min(float(np.min(np.cos(curl(t, a, b))))
                                  for a, b in ((0, 1), (0, 2), (1, 2))))
        field = rng.normal(size=t.shape)
        for name in masks:
            min_q[name] = min(min_q[name], raw_q(t, field, masks[name]) / np.sum(field**2))
        # Dense spectrum only for n=4: 192x192 doubles, not the full headline form.
        if n == 4:
            H = np.zeros((3*n**3, 3*n**3))
            for p in plaquettes(n):
                x, a, b = p
                if not masks["corner"][a, b][x]:
                    continue
                ids = [((e[0][0]*n + e[0][1])*n + e[0][2])*3 + e[1] for e in edges(p, n)]
                v = np.array([1., 1., -1., -1.])
                H[np.ix_(ids, ids)] += np.cos(curl(t, a, b)[x]) * np.outer(v, v)
            eig_min.append(float(np.linalg.eigvalsh(H)[0]))
    assert min_cos > 0 and min(min_q.values()) > 0
    assert not eig_min or min(eig_min) > -1e-10
    return {"N": n, "ell": ell, "k": k, "a0": a0, "trials": trials,
            "global_three_bound_max_ratio": max_ratio, "max_link_phase": max_phase,
            "min_cos_plaquette_flux": min_cos, "min_sampled_raw_rayleigh": min_q,
            "corner_dense_minimum": min(eig_min) if eig_min else None,
            "scope": "raw Cartan Delta only; no full InstIneqS, tower or threshold certificate"}


def main():
    rng = np.random.default_rng(20261021)
    result = {"finite_coverage": finite_coverage(),
              "hidden_bond_scan": [hidden_bond_scan(n, w) for n, w in ((4, 2), (6, 2), (8, 2), (16, 8))],
              "small_phase": [small_phase_search(n, a0, 4, rng)
                              for n in (4, 16) for a0 in (np.pi / (2*np.sqrt(2)), 0.1, 0.01)],
              "closed_negative_goal": False}
    out = Path(__file__).with_name("search.json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
