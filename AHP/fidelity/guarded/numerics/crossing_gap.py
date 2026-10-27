#!/usr/bin/env python3
"""
Gap of deltaK along an exterior-only path, and whether a one-bond interior
defect (nonzero plaqIn holonomy) moves the near-zero eigenvalue.

Same transcriptions as delta_pencil_probe.py.
The correction used here is the finite difference of deltaK in the interior
bond. It is NOT Delta2 (R2Algebra.lean:220). Evidence only.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np

import delta_pencil_probe as P

OUT = Path(__file__).resolve().parent / "crossing_results.json"


def pick_interior_bond(lat: P.Lattice):
    for b in lat.both:
        if b[1] == 0:
            return b
    raise RuntimeError("no both-in bond")


def gap_stats(ev, cut=1e-8):
    ev = np.asarray(ev)
    return {
        "min": float(ev[0]),
        "max": float(ev[-1]),
        "n_neg": int(np.sum(ev < -cut)),
        "n_small": int(np.sum(np.abs(ev) <= 1e-6)),
        "min_abs": float(np.min(np.abs(ev))),
        "max_neg": float(np.max(ev[ev < -cut])) if np.any(ev < -cut) else None,
        "min_pos": float(np.min(ev[ev > cut])) if np.any(ev > cut) else None,
    }


def analyze(N, box, thetas, eps_list):
    lat = P.Lattice(N, box)
    lat._cache_sets()
    ib = pick_interior_bond(lat)
    lat.interior_bond = ib
    print(f"N={N} interior bond {ib} dim {lat.dim} plaqIn {len(lat.plaq_in)}", flush=True)
    # holonomy check at eps
    U = lat.config(0.0, 0.3)
    hol_in = []
    for p in lat.plaq_in:
        if ib in lat.edges_of(p):
            H = lat.holonomy(U, p)
            hol_in.append(float(np.trace(H).real))
    print("  plaqIn traces through the defect", hol_in, "im", lat.im_hol_energy(U), flush=True)
    rows = []
    cache = {}
    for eps in eps_list:
        for th in thetas:
            U = lat.config(th, eps)
            M = lat.delta_matrix(U, "all")
            ev = np.linalg.eigvalsh(M)
            st = gap_stats(ev)
            st.update({"eps": eps, "theta": th})
            rows.append(st)
            cache[(eps, th)] = M
            print(
                f"  eps={eps:.3f} θ={th:.4f} min={st['min']:.4e} minabs={st['min_abs']:.4e} "
                f"nsmall={st['n_small']} nneg={st['n_neg']}",
                flush=True,
            )
    # near-zero vector of the flat-interior path, quadratic form of the interior difference
    aligns = []
    for th in thetas:
        M0 = cache[(0.0, th)]
        ev, evec = np.linalg.eigh(M0)
        # eigenvector of smallest |eigenvalue|
        k = int(np.argmin(np.abs(ev)))
        v = evec[:, k]
        for eps in eps_list:
            if eps == 0.0:
                continue
            Dfd = cache[(eps, th)] - M0
            q = float(v @ Dfd @ v)
            op = float(np.linalg.norm(Dfd, 2))
            # pencil = M0 - Dfd = 2 M0 - M_eps, and M_eps = M0 + Dfd
            evP = np.linalg.eigvalsh(M0 - Dfd)
            evC = ev
            aligns.append({
                "theta": th,
                "eps": eps,
                "carrier_eig_closest": float(ev[k]),
                "carrier_min_abs": float(np.min(np.abs(evC))),
                "v_Dfd_v": q,
                "Dfd_opnorm": op,
                "pencil_min_abs": float(np.min(np.abs(evP))),
                "pencil_min": float(evP[0]),
                "carrier_indef_invertible": bool(ev[0] < -1e-6 and np.min(np.abs(evC)) > 1e-5),
                "pencil_singular_carrier_not": bool(
                    np.min(np.abs(evC)) > 1e-4 and np.min(np.abs(evP)) < 1e-5
                ),
                "pencil_neg_carrier_pos": bool(ev[0] > 1e-5 and evP[0] < -1e-5),
            })
    # localized delta change at theta=0
    Uflat = lat.config(0.0, 0.0)
    Udef = lat.config(0.0, 0.2)
    Din0 = lat.delta_matrix(Uflat, "in")
    Din1 = lat.delta_matrix(Udef, "in")
    loc = {
        "delta_in_diff_opnorm_eps_0.2": float(np.linalg.norm(Din1 - Din0, 2)),
        "delta_in_flat_min": float(np.linalg.eigvalsh(Din0)[0]),
        "im": lat.im_hol_energy(Udef),
    }
    print("  local", loc, flush=True)
    return {
        "N": N,
        "box": box,
        "interior_bond": list(ib[0]) + [ib[1]],
        "flat_kernel_guess": 3 * (N**3) + 6,
        "hol_traces": hol_in,
        "rows": rows,
        "aligns": aligns,
        "local": loc,
    }


def main():
    thetas = [0.0, 0.05, 0.1, 0.2, 0.4, np.pi / 8, np.pi / 4, np.pi / 2, np.pi]
    eps_list = [0.0, 0.05, 0.2]
    results = [analyze(3, 2, thetas, eps_list), analyze(4, 2, thetas, [0.0, 0.2])]
    OUT.write_text(json.dumps({"results": results}, indent=2))
    print("wrote", OUT, flush=True)


if __name__ == "__main__":
    main()
