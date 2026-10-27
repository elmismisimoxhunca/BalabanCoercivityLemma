#!/usr/bin/env python3
"""ATTACK checks for the s1-touching stage-A design. Evidence only, not a theorem.

Checks:
1. The SPEC sentence "The mode that realises -0.22 has curl energy +0.024 and
   Delta' energy -0.281 ... flat divergence energy about 4.6" is not computed by
   shell_touch.py (eigvalsh only). Reconstruct both eps=0.05 link configs the
   recorded runs used (the main()-sequence one behind min -0.2233 and the fresh
   seed-0 one behind raw min -0.2573), compute the minimising eigenvector, and
   decompose Q into the curl (hsInner) part and the bilPlaq part, plus the flat
   divergence energy. Operators transcribed as in shell_touch.py:
   curlValueCovariant CovariantOperators.lean:315, bilPlaq_atoms
   DeltaPrimeOperator.lean:433, hsInner SuTwoInner.lean:104, divergence penalty
   is the script's own flat U=1 model (not Lean's R D*).
2. CubeBond(Omega) subset of ReadBond(Omega) on the five geometries (the
   inclusion behind "ClassCoupledShell -> ClassCoupled", ZStatementP428.lean:145
   vs the SPEC's ReadBond).
3. The phase-cap arithmetic: a0/(sqrt(2) ell^j) and |phi| <= 2|Delta theta|.
4. Monotonicity core of the rewrite obstruction: every touching plaquette has
   all corners in the forced corner set C, and plaqIn(C) contains a plaquette
   with no corner in Omega (so no S superset C can work either).
"""

from __future__ import annotations

import json
import sys

import numpy as np
from numpy.linalg import eigh, eigvalsh

sys.path.insert(0, "/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s1-touching/numerics")
import shell_touch as st


def replay_rng_to_nonabelian():
    """Replay main()'s rng draws up to (but not including) nonabelian_min_eig."""
    rng = np.random.default_rng(0)
    # shells: 6 calls, 400 trials each; per trial one scalar then one (4,3) draw
    for theta_max, _, _ in (
        (np.pi, np.pi, "no_bound"),
        (np.pi / 2, np.pi / 2, "half"),
        (np.pi / 4, np.pi / 4, "quarter"),
        (np.pi / 8, np.pi / 8, "eighth"),
        (0.5, 0.5, "half_rad"),
        (np.pi / (2 * np.sqrt(2)), np.pi / (2 * np.sqrt(2)), "a0cap"),
    ):
        for _ in range(400):
            rng.uniform(-theta_max, theta_max)
            rng.uniform(-theta_max, theta_max, size=(4, 3))
    # random_cartan_N6 draws
    N = 6
    Omega = st.slab_mask(N, 2)
    plaquettes = st.all_plaquettes(N)
    read = st.bond_sets(N, Omega, plaquettes)[2]
    read_ids = [st.bond_id(b[0], b[1], N) for b in read]
    for theta_max, ntry in ((np.pi / 2, 8), (np.pi / 4, 8), (np.pi / 8, 6), (0.3, 6)):
        for _ in range(ntry):
            rng.uniform(-theta_max, theta_max, size=len(read_ids))
    return rng


def links_from_coeff(coeff):
    from scipy.linalg import expm

    n_bonds = coeff.shape[0]
    return np.stack(
        [expm(coeff[b, 0] * st.T1 + coeff[b, 1] * st.T2 + coeff[b, 2] * st.T3) for b in range(n_bonds)]
    )


def assemble_parts(N, plaquettes, U):
    """Hessians of the curl (hsInner) part and of 1/2 bilPlaq, separately."""
    n_bonds = 3 * N ** 3
    dim = 3 * n_bonds
    Hc = np.zeros((dim, dim))
    Hb = np.zeros((dim, dim))
    eye = np.eye(12)

    def parts(p, comps):
        es = st.edges_of(*p, N)
        ids = [st.bond_id(e[0], e[1], N) for e in es]
        Um = [U[i] for i in ids]
        A = [comps[i, 0] * st.T1 + comps[i, 1] * st.T2 + comps[i, 2] * st.T3 for i in range(4)]
        cmat = A[0] + Um[0] @ A[1] @ Um[0].conj().T - Um[3] @ A[2] @ Um[3].conj().T - A[3]
        hs = st.hs_mat(cmat)
        Hhol = Um[0] @ Um[1] @ Um[2].conj().T @ Um[3].conj().T
        re = 0.5 * (Hhol + Hhol.conj().T)
        im = (1.0 / (2j)) * (Hhol - Hhol.conj().T)
        ic = 1j * cmat
        first = float(np.trace(ic @ ic @ (re - st.I2)).real)
        AZW = -(Um[3] @ A[2] @ Um[3].conj().T)
        AWX = -A[3]
        AXY = A[0]
        AYZ = Um[0] @ A[1] @ Um[0].conj().T
        bs = [1j * M for M in (AZW, AWX, AXY, AYZ)]
        second = 0.0
        for i, j in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
            second += float(np.trace((1j * bs[i]) @ bs[j] @ im).real - np.trace((1j * bs[j]) @ bs[i] @ im).real)
        return hs, 0.5 * (first + second)

    for p in plaquettes:
        es = st.edges_of(*p, N)
        ids = [st.bond_id(e[0], e[1], N) for e in es]
        lc = np.zeros((12, 12))
        lb = np.zeros((12, 12))
        dc = np.zeros(12)
        db = np.zeros(12)
        for a in range(12):
            dc[a], db[a] = parts(p, eye[a].reshape(4, 3))
            lc[a, a] = dc[a]
            lb[a, a] = db[a]
        for a in range(12):
            for b in range(a + 1, 12):
                qc, qb = parts(p, (eye[a] + eye[b]).reshape(4, 3))
                lc[a, b] = lc[b, a] = 0.5 * (qc - dc[a] - dc[b])
                lb[a, b] = lb[b, a] = 0.5 * (qb - db[a] - db[b])
        gids = [3 * b + c for b in ids for c in range(3)]
        for a in range(12):
            for b in range(12):
                Hc[gids[a], gids[b]] += lc[a, b]
                Hb[gids[a], gids[b]] += lb[a, b]
    return Hc, Hb


def flat_divergence_form(N):
    n_bonds = 3 * N ** 3
    dim = 3 * n_bonds
    G = np.zeros((dim, dim))
    for x0 in range(N):
        for x1 in range(N):
            for x2 in range(N):
                x = (x0, x1, x2)
                for comp in range(3):
                    terms = []
                    for mu in range(3):
                        bf = st.bond_id(x, mu, N)
                        xb = list(x)
                        xb[mu] = (xb[mu] - 1) % N
                        bb = st.bond_id(tuple(xb), mu, N)
                        terms.append((3 * bf + comp, 1.0))
                        terms.append((3 * bb + comp, -1.0))
                    for i, ci in terms:
                        for j, cj in terms:
                            G[i, j] += ci * cj
    return G


def decompose(label, N, coeff):
    Omega = st.slab_mask(N, 2)
    plaquettes = st.select(st.all_plaquettes(N), Omega, N, "touch")
    U = links_from_coeff(coeff)
    Hc, Hb = assemble_parts(N, plaquettes, U)
    H = Hc + Hb
    ev, vec = eigh(H)
    v = vec[:, 0]
    G = flat_divergence_form(N)
    out = {
        "label": label,
        "min_eig": float(ev[0]),
        "curl_part": float(v @ Hc @ v),
        "bilplaq_part": float(v @ Hb @ v),
        "sum": float(v @ H @ v),
        "flat_div_energy": float(v @ G @ v),
        "eigvalsh_min_check": float(eigvalsh(H)[0]),
    }
    return out


def main():
    report = {}

    # 1. eigenmode decomposition, both recorded configs
    rng = replay_rng_to_nonabelian()
    n_bonds4 = 3 * 4 ** 3
    rng.uniform(-0.0, 0.0, size=(n_bonds4, 3))  # the eps=0.0 draw
    coeff_main = rng.uniform(-0.05, 0.05, size=(n_bonds4, 3))  # behind min -0.2233
    rows = [decompose("main_sequence_eps0.05 (min -0.2233 row)", 4, coeff_main)]
    rng_seed0 = np.random.default_rng(0)
    coeff_seed0 = rng_seed0.uniform(-0.05, 0.05, size=(n_bonds4, 3))  # behind raw -0.2573
    rows.append(decompose("gauge_penalty_seed0_eps0.05 (raw min -0.2573 row)", 4, coeff_seed0))
    report["eigenmode_decomposition"] = rows

    # 2. CubeBond subset ReadBond on the five geometries
    inclusions = []
    for N, width, label in ((4, 2, "slab_N4_W2"), (6, 2, "slab_N6_W2"), (6, 4, "slab_N6_W4"),
                            (8, 2, "slab_N8_W2"), (8, 4, "cube_compare")):
        Omega = st.cube_mask(N, 2) if label == "cube_compare" else st.slab_mask(N, width)
        plaquettes = st.all_plaquettes(N)
        touch, both, read, far = st.bond_sets(N, Omega, plaquettes)
        inclusions.append({
            "label": label,
            "cubeBond_subset_readBond": bool(both <= read),
            "cubeBond_subset_touchBond": bool(both <= touch),
            "n_both": len(both), "n_read": len(read),
        })
    report["bond_inclusions"] = inclusions

    # 3. cap arithmetic
    caps = {}
    for a0, j in ((np.pi / (2 * np.sqrt(2)), 0), (np.pi / np.sqrt(2), 0), (np.pi * np.sqrt(2), 0)):
        phase = a0 / (np.sqrt(2) * (2.0 ** j))
        caps[f"a0={a0:.6f}"] = {"phase_cap_j0": float(phase), "two_diff_bound_j0": float(2 * phase),
                                 "cos_nonneg_guaranteed": bool(2 * phase <= np.pi / 2 + 1e-12)}
    report["cap_arithmetic"] = caps

    # 4. rewrite obstruction monotonicity core (side 4 width 2 and the cube)
    rew = []
    for N, width, label in ((4, 2, "slab_N4_W2"), (8, 4, "cube_compare")):
        Omega = st.cube_mask(N, 2) if label == "cube_compare" else st.slab_mask(N, width)
        plaquettes = st.all_plaquettes(N)
        touch_ps = [p for p in plaquettes if st.plaq_kind(p, Omega, N) != "out"]
        C = set()
        for p in touch_ps:
            C.update(st.corners_of(*p, N))
        all_corners_forced = all(all(c in C for c in st.corners_of(*p, N)) for p in touch_ps)
        witness = [p for p in plaquettes
                   if all(c in C for c in st.corners_of(*p, N)) and st.plaq_kind(p, Omega, N) == "out"]
        # for ANY S with plaqIn S = plaqCorner Omega, S must contain C; then plaqIn S
        # contains the witness plaquettes (monotonicity), so equality fails.
        rew.append({"label": label,
                    "all_touching_corners_forced": bool(all_corners_forced),
                    "n_witness_plaquettes_in_plaqIn_C_outside_plaqCorner": len(witness),
                    "rewrite_impossible_for_any_S": bool(all_corners_forced and len(witness) > 0)})
    report["rewrite_monotonicity"] = rew

    out = "/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s1-touching/numerics/attack_check.json"
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
