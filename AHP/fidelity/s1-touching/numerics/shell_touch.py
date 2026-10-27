#!/usr/bin/env python3
"""Numerical evidence for the s1-touching shell variant. Not a proof and not a theorem.

Every operator below is a transcription of a frozen Lean definition. Citations are
file:line of the definition or the identity being checked.

Cartan quadratic form of localised Delta (eta = 1, the Lean body):
  Q(A) = sum_p (hsInner(curl, curl) + (1/2) bilPlaq)
  D1Eval.lean:56 delta_form_sum
  D1Eval.lean:28 plaq_central (holonomy -1 => contribution -hsInner(curl,curl))
  D1Eval2.lean:152 delta_value / D1Geo1.lean:94 BdPt.delta_pi
    (four plaquettes on the outward bond, holonomy -1 => Q = -4 hsInner)
  CovariantOperators.lean:315 curlValueCovariant
  CovariantOperators.lean:247 RMap (U X U^H)
  SuTwoInner.lean:104 hsInner = -1/2 Re tr(XY) on traceless skew-Hermitian matrices
  DeltaPrime.lean:106 holonomyElem = periodicPlaquetteHolonomy (ClayStatement.lean:1286)
  DeltaPrime.lean:125 reHolonomy, :133 imHolonomy
  DeltaPrimeOperator.lean:433 bilPlaq_atoms (raw trace, six Im brackets + first term)
  ZR2Ops2.lean:74 plaqIn (all four endpoints in the set)
  ZStatementP428.lean:145 CubeBond (both endpoints)
  D1Path.lean:25 Zb, :46 Uth (diag(e^{i theta}, e^{-i theta}) on bonds with no endpoint in Omega)

Plaquette corners use periodicLatticeShift (ClayStatement.lean:1281) and the four
boundary edges (ClayStatement.lean:1295).
"""

from __future__ import annotations

import json
import time

import numpy as np
from numpy.linalg import eigvalsh

# su(2) basis, CovariantOperators.lean:128 witness is T1.
T1 = np.array([[1j, 0.0], [0.0, -1j]], dtype=np.complex128)
T2 = np.array([[0.0, 1.0], [-1.0, 0.0]], dtype=np.complex128)
T3 = np.array([[0.0, 1j], [1j, 0.0]], dtype=np.complex128)
BASIS = (T1, T2, T3)
I2 = np.eye(2, dtype=np.complex128)


def hs_mat(X: np.ndarray) -> float:
    """SuTwoInner.lean:104, X skew-Hermitian traceless."""
    return float((-0.5 * np.trace(X @ X)).real)


def frob(M: np.ndarray) -> float:
    """RMapLipschitz.lean:60 frobSq = sum |entries|^2, frobNorm = sqrt."""
    return float(np.sqrt(np.sum(np.abs(M) ** 2)))


def shift(x, mu, N):
    y = list(x)
    y[mu] = (y[mu] + 1) % N
    return (y[0], y[1], y[2])


def bond_id(x, mu, N):
    return ((x[0] * N + x[1]) * N + x[2]) * 3 + mu


def edges_of(x, mu, nu, N):
    """Boundary edges in holonomy order. ClayStatement.lean:1295, mu < nu.
    (x,mu), (x+mu,nu), (x+nu,mu), (x,nu)."""
    return (
        (x, mu),
        (shift(x, mu, N), nu),
        (shift(x, nu, N), mu),
        (x, nu),
    )


def corners_of(x, mu, nu, N):
    xm = shift(x, mu, N)
    xn = shift(x, nu, N)
    return (x, xm, xn, shift(xm, nu, N))


def all_plaquettes(N):
    out = []
    for x0 in range(N):
        for x1 in range(N):
            for x2 in range(N):
                x = (x0, x1, x2)
                for mu, nu in ((0, 1), (0, 2), (1, 2)):
                    out.append((x, mu, nu))
    return out


def slab_mask(N, width):
    return {(x0, x1, x2) for x0 in range(width) for x1 in range(N) for x2 in range(N)}


def cube_mask(N, M):
    return {(x0, x1, x2) for x0 in range(M) for x1 in range(M) for x2 in range(M)}


def plaq_kind(p, Omega, N):
    """Return 'in' if all 4 corners in Omega (plaqIn), 'touch' if >=1, else 'out'."""
    x, mu, nu = p
    cs = corners_of(x, mu, nu, N)
    k = sum(c in Omega for c in cs)
    if k == 4:
        return "in"
    if k >= 1:
        return "touch"
    return "out"


def select(plaquettes, Omega, N, mode):
    chosen = []
    for p in plaquettes:
        k = plaq_kind(p, Omega, N)
        if mode == "all" or (mode == "in" and k == "in") or (mode == "touch" and k != "out"):
            chosen.append(p)
    return chosen


def cartan_hessian(N, plaquettes, phases, mode_cos_only=True):
    """Assemble a^T H a = sum_p cos(phi_p) curl(a)^2 on the Cartan sector.

    Closed form, valid when every link is diag(e^{i theta}, e^{-i theta}) and the
    test field is a real multiple of T1. Second bilPlaq brackets then have trace 0
    (checked in unit_tests). curl scalar = a0 + a1 - a2 - a3, CovariantOperators.lean:315
    with RMap = id on the Cartan.
    """
    n = 3 * N ** 3
    H = np.zeros((n, n), dtype=np.float64)
    v = np.array([1.0, 1.0, -1.0, -1.0])
    outer = np.outer(v, v)
    for (x, mu, nu) in plaquettes:
        es = edges_of(x, mu, nu, N)
        th = [phases[bond_id(e[0], e[1], N)] for e in es]
        phi = th[0] + th[1] - th[2] - th[3]
        w = float(np.cos(phi))
        if w == 0.0:
            continue
        ids = [bond_id(e[0], e[1], N) for e in es]
        block = w * outer
        for i in range(4):
            for j in range(4):
                H[ids[i], ids[j]] += block[i, j]
    return H


def rayleigh_bond(H, N, x, mu):
    i = bond_id(x, mu, N)
    return float(H[i, i])


def spectrum_stats(H, tol=1e-8):
    ev = eigvalsh(H)
    return {
        "min": float(ev[0]),
        "max": float(ev[-1]),
        "n_neg": int(np.sum(ev < -tol)),
        "n_zero": int(np.sum(np.abs(ev) <= tol)),
        "dim": int(ev.shape[0]),
    }


def phases_uth(N, Omega, theta):
    """D1Path.lean:46. Nonzero only on Zb: neither endpoint in Omega."""
    ph = np.zeros(3 * N ** 3, dtype=np.float64)
    for x0 in range(N):
        for x1 in range(N):
            for x2 in range(N):
                x = (x0, x1, x2)
                for mu in range(3):
                    y = shift(x, mu, N)
                    if x not in Omega and y not in Omega:
                        ph[bond_id(x, mu, N)] = theta
    return ph


def bond_sets(N, Omega, plaquettes):
    """TouchBond of Omega vs ReadBond (edge of a plaquette with a corner in Omega)
    vs CubeBond-style both-endpoints (frozen CubeBond on the site set Omega)."""
    touch, both, read = set(), set(), set()
    far = set()
    for x0 in range(N):
        for x1 in range(N):
            for x2 in range(N):
                x = (x0, x1, x2)
                for mu in range(3):
                    y = shift(x, mu, N)
                    b = (x, mu)
                    inn = x in Omega
                    iny = y in Omega
                    if inn or iny:
                        touch.add(b)
                    if inn and iny:
                        both.add(b)
                    if not inn and not iny:
                        far.add(b)
    for p in plaquettes:
        if plaq_kind(p, Omega, N) == "out":
            continue
        for e in edges_of(*p, N):
            read.add(e)
    return touch, both, read, far


def exit_site(N, width):
    """Boundary site of the slab x0 < width, outward direction 0. D1Geo1.lean BdPt."""
    return (width - 1, 0, 0)


def neighborhood(Omega, N):
    out = set(Omega)
    for x in Omega:
        for mu in range(3):
            out.add(shift(x, mu, N))
            y = list(x)
            y[mu] = (y[mu] - 1) % N
            out.add(tuple(y))
            # l_infty 1 also needs diagonal steps; generate by repeating face steps
    # close under one more face step from the new sites, three times is enough for l1,
    # but corners of touching plaquettes are exactly l_infty <= 1.
    seeds = list(Omega)
    out = set(Omega)
    for x in seeds:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for dz in (-1, 0, 1):
                    out.add(((x[0] + dx) % N, (x[1] + dy) % N, (x[2] + dz) % N))
    return out


def rewrite_obstruction(N, Omega, plaquettes):
    """If S contains every corner of every touching plaquette, plaqIn(S) contains
    an outer face plaquette that does not meet Omega. Then no site set realises
    plaqIn(S) = plaqCorner(Omega)."""
    touch_ps = [p for p in plaquettes if plaq_kind(p, Omega, N) != "out"]
    in_ps = [p for p in plaquettes if plaq_kind(p, Omega, N) == "in"]
    corners = set()
    for p in touch_ps:
        corners.update(corners_of(*p, N))
    extra = []
    for p in plaquettes:
        cs = corners_of(*p, N)
        if all(c in corners for c in cs) and plaq_kind(p, Omega, N) == "out":
            extra.append(p)
            if len(extra) >= 3:
                break
    # Also record whether the forced corner set is an M-block union for M=2.
    def block_closed(S, M):
        blocks = {}
        for x in S:
            key = (x[0] // M, x[1] // M, x[2] // M)
            blocks.setdefault(key, 0)
            blocks[key] += 1
        full = M ** 3
        return all(v == full for v in blocks.values()) and len(S) == len(blocks) * full

    return {
        "n_touch": len(touch_ps),
        "n_in": len(in_ps),
        "n_all": len(plaquettes),
        "touch_minus_in": len(touch_ps) - len(in_ps),
        "forced_corners": len(corners),
        "outer_plaquettes_in_plaqIn_of_forced": len(extra),
        "example_outer": [
            {"base": list(p[0]), "dirs": [p[1], p[2]], "corners": [list(c) for c in corners_of(*p, N)]}
            for p in extra[:1]
        ],
        "forced_is_M2_block_closed": block_closed(corners, 2) if N % 2 == 0 else None,
        "omega_is_M2_block_closed": block_closed(Omega, 2) if N % 2 == 0 else None,
        "one_neighborhood_equals_omega": neighborhood(Omega, N) == Omega,
        "rewrite_impossible": len(extra) > 0,
    }


def unit_tests():
    """Match BdPt.delta_pi and the Cartan closed form against the matrix transcription."""

    def hol(phi):
        return np.diag([np.exp(1j * phi), np.exp(-1j * phi)])

    def rmap(U, X):
        return U @ X @ U.conj().T

    def bil_and_q(a, phi, link_phases=None):
        """One plaquette. a is length-4 Cartan coefficients of T1.
        link_phases defaults to a pure-holonomy representative (phi on edge 0)."""
        if link_phases is None:
            link_phases = (phi, 0.0, 0.0, 0.0)
        Us = [hol(th) for th in link_phases]
        # curl, RMap of diagonal U on T1 is T1
        cmat = (
            a[0] * T1
            + rmap(Us[0], a[1] * T1)
            - rmap(Us[3], a[2] * T1)
            - a[3] * T1
        )
        hs = hs_mat(cmat)
        H = hol(link_phases[0] + link_phases[1] - link_phases[2] - link_phases[3])
        Hinv = H.conj().T
        re = 0.5 * (H + Hinv)
        im = (1.0 / (2j)) * (H - Hinv)
        ic = 1j * cmat
        first = float(np.trace(ic @ ic @ (re - I2)).real)
        # A' in b-order a1=ZW, a2=WX, a3=XY, a4=YZ. DeltaPrimeOperator.lean:287-334.
        AZW = -rmap(Us[3], a[2] * T1)
        AWX = -(a[3] * T1)
        AXY = a[0] * T1
        AYZ = rmap(Us[0], a[1] * T1)
        bs = [1j * M for M in (AZW, AWX, AXY, AYZ)]
        second = 0.0
        for i, j in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
            second += float(np.trace((1j * bs[i]) @ bs[j] @ im).real)
            second -= float(np.trace((1j * bs[j]) @ bs[i] @ im).real)
        bil = first + second
        Q = hs + 0.5 * bil
        return Q, second, hs

    checks = []
    for phi, expect in ((0.0, 1.0), (np.pi / 2, 0.0), (np.pi, -1.0), (np.pi / 3, np.cos(np.pi / 3))):
        Q, second, hs = bil_and_q(np.array([1.0, 0.0, 0.0, 0.0]), phi)
        checks.append(
            {
                "phi": phi,
                "Q": Q,
                "second": second,
                "expect_cos": expect,
                "ok": abs(Q - expect) < 1e-9 and abs(second) < 1e-9,
            }
        )
    # two-edge field, second bracket should still vanish in the Cartan
    Q2, second2, _ = bil_and_q(np.array([0.3, -0.7, 0.2, 0.5]), 0.8)
    c = 0.3 - 0.7 - 0.2 - 0.5
    # wait curl = a0 + a1 - a2 - a3 = 0.3 + (-0.7) - 0.2 - 0.5
    c = 0.3 + (-0.7) - 0.2 - 0.5
    expect2 = (c ** 2) * np.cos(0.8)
    checks.append(
        {
            "two_edge": True,
            "Q": Q2,
            "second": second2,
            "expect": expect2,
            "ok": abs(Q2 - expect2) < 1e-9 and abs(second2) < 1e-9,
        }
    )
    # hermitian smallness constant: A = theta * diag(1,-1), frob = sqrt(2) |theta|
    A = np.diag([1.0, -1.0])
    checks.append({"frob_diag": frob(A), "expect_sqrt2": float(np.sqrt(2.0)), "ok": abs(frob(A) - np.sqrt(2)) < 1e-12})
    # hsInner(T1,T1) = 1
    checks.append({"hs_T1": hs_mat(T1), "ok": abs(hs_mat(T1) - 1.0) < 1e-12})
    assert all(c["ok"] for c in checks), checks
    return checks


def four_plaquette_rayleigh(N, width, theta):
    """Global check of BdPt.delta_pi on a slab: field on the outward bond.
    Touching and all-plaquette selections both include the four plaquettes;
    plaqIn includes none of them, so its Rayleigh quotient is 0."""
    Omega = slab_mask(N, width)
    plaquettes = all_plaquettes(N)
    ph = phases_uth(N, Omega, theta)
    x = exit_site(N, width)
    out = {}
    for mode in ("touch", "in", "all"):
        chosen = select(plaquettes, Omega, N, mode)
        H = cartan_hessian(N, chosen, ph)
        out[mode] = rayleigh_bond(H, N, x, 0)
    out["expect_touch"] = float(4.0 * np.cos(theta))
    out["ok"] = (
        abs(out["touch"] - 4.0 * np.cos(theta)) < 1e-8
        and abs(out["all"] - 4.0 * np.cos(theta)) < 1e-8
        and abs(out["in"]) < 1e-8
    )
    return out


def max_curl_under_bounds(theta_max, delta_max, trials, rng):
    """Minimise sum of cos phi over the four plaquettes incident to one bond,
    with |theta| <= theta_max on every edge and |parallel difference| <= delta_max.
    Returns the most negative sum found (each plaquette contributes cos phi to the
    single-bond Rayleigh quotient) and whether a negative value was seen."""
    # 4 plaquettes, 3 private edges each, plus the shared bond: 1 + 12 = 13 phases,
    # but parallel-difference constraints couple them. Free optimisation by random
    # projection onto the box, then a few coordinate sweeps.
    # Edges: shared s; for each of 4 plaquettes, three edges e[k][0..2] in holonomy
    # positions (the shared bond occupies a known slot).
    # We only enforce |theta|<=theta_max and, for the two parallel pairs inside each
    # plaquette, |difference|<=delta_max. That is necessary for the gradient clause
    # but not a full lattice gradient field; it is an UPPER bound on how negative
    # the Rayleigh quotient can be made (the real gradient field is more constrained).
    best = 4.0
    best_phi = None
    for _ in range(trials):
        s = rng.uniform(-theta_max, theta_max)
        edges = rng.uniform(-theta_max, theta_max, size=(4, 3))
        # project parallel differences: slot layout per plaquette
        # P1-type: phi = s + e0 - e1 - e2, differences (s - e2) and (e0 - e1) if we
        # identify e2 as the parallel of s and e1 as the parallel of e0.
        # We resample violating coordinates toward the shared bond.
        for _sweep in range(6):
            for k in range(4):
                # keep e2 within delta of s, e1 within delta of e0
                if abs(edges[k, 2] - s) > delta_max:
                    edges[k, 2] = np.clip(s + np.sign(edges[k, 2] - s) * delta_max, -theta_max, theta_max)
                if abs(edges[k, 1] - edges[k, 0]) > delta_max:
                    edges[k, 1] = np.clip(
                        edges[k, 0] + np.sign(edges[k, 1] - edges[k, 0]) * delta_max,
                        -theta_max,
                        theta_max,
                    )
        phis = []
        for k in range(4):
            phis.append(s + edges[k, 0] - edges[k, 1] - edges[k, 2])
        val = float(np.sum(np.cos(phis)))
        if val < best:
            best = val
            best_phi = [float(p) for p in phis]
    # analytic corner: phi = 2*delta_max on every plaquette (two differences of size delta)
    phi_cap = min(np.pi, 2.0 * delta_max)
    analytic = float(4.0 * np.cos(phi_cap))
    return {"random_min_sum_cos": best, "phis": best_phi, "analytic_4cos_of_2delta": analytic}


def nonabelian_min_eig(N, Omega, eps_scale, rng, mode="touch"):
    """Spectrum of the full su(2) quadratic form on a small torus.

    Links U = expm(eps) with eps = sum c_a T_a, each |c| <= eps_scale
    (the anti-Hermitian coefficient; frob of the hermitian generator is sqrt(2)|c|
    for a single component). Test fields have 3 components per bond.
    """
    from scipy.linalg import expm

    plaquettes = select(all_plaquettes(N), Omega, N, mode)
    n_bonds = 3 * N ** 3
    dim = 3 * n_bonds
    # link coefficients, shape (n_bonds, 3)
    coeff = rng.uniform(-eps_scale, eps_scale, size=(n_bonds, 3))
    U = []
    for b in range(n_bonds):
        eps = coeff[b, 0] * T1 + coeff[b, 1] * T2 + coeff[b, 2] * T3
        U.append(expm(eps))
    U = np.stack(U, axis=0)

    def field_from_local(ids, comps):
        """comps: (4,3) coefficients on the four edges."""
        mats = []
        for i in range(4):
            mats.append(comps[i, 0] * T1 + comps[i, 1] * T2 + comps[i, 2] * T3)
        return mats

    def Q_of(p, comps):
        x, mu, nu = p
        es = edges_of(x, mu, nu, N)
        ids = [bond_id(e[0], e[1], N) for e in es]
        Um = [U[i] for i in ids]
        A = field_from_local(ids, comps)
        # curl
        cmat = A[0] + (Um[0] @ A[1] @ Um[0].conj().T) - (Um[3] @ A[2] @ Um[3].conj().T) - A[3]
        hs = hs_mat(cmat)
        # holonomy Umu * Unu_shift * Umu_shift^{-1} * Unu^{-1}
        H = Um[0] @ Um[1] @ Um[2].conj().T @ Um[3].conj().T
        re = 0.5 * (H + H.conj().T)
        im = (1.0 / (2j)) * (H - H.conj().T)
        ic = 1j * cmat
        first = float(np.trace(ic @ ic @ (re - I2)).real)
        AZW = -(Um[3] @ A[2] @ Um[3].conj().T)
        AWX = -A[3]
        AXY = A[0]
        AYZ = Um[0] @ A[1] @ Um[0].conj().T
        bs = [1j * M for M in (AZW, AWX, AXY, AYZ)]
        second = 0.0
        for i, j in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
            second += float(np.trace((1j * bs[i]) @ bs[j] @ im).real)
            second -= float(np.trace((1j * bs[j]) @ bs[i] @ im).real)
        return hs + 0.5 * (first + second)

    # Assemble Hessian on the bonds that appear; others stay 0.
    H = np.zeros((dim, dim), dtype=np.float64)
    eye = np.eye(12)
    for p in plaquettes:
        x, mu, nu = p
        es = edges_of(*p, N)
        ids = [bond_id(e[0], e[1], N) for e in es]
        # local index k = edge*3 + comp
        local = np.zeros((12, 12), dtype=np.float64)
        diagQ = np.zeros(12)
        for a in range(12):
            comps = eye[a].reshape(4, 3)
            diagQ[a] = Q_of(p, comps)
            local[a, a] = diagQ[a]
        for a in range(12):
            for b in range(a + 1, 12):
                comps = (eye[a] + eye[b]).reshape(4, 3)
                q = Q_of(p, comps)
                local[a, b] = local[b, a] = 0.5 * (q - diagQ[a] - diagQ[b])
        gids = []
        for e_i, b in enumerate(ids):
            for c in range(3):
                gids.append(3 * b + c)
        for a in range(12):
            for b in range(12):
                H[gids[a], gids[b]] += local[a, b]
    # Restrict to bonds with a nonzero row so the unused-bond kernel is not the story,
    # but still report the full minimum (unused bonds contribute exact zeros).
    stats = spectrum_stats(H)
    stats["eps_scale"] = float(eps_scale)
    stats["n_plaquettes"] = len(plaquettes)
    stats["max_link_frob_herm"] = float(np.sqrt(2.0) * np.max(np.abs(coeff)))
    return stats


def gauge_penalty_compare(eps, N=4, width=2, lam=1.0, seed=0):
    """min eigenvalue of raw Delta and of Delta + lam * ||flat div||^2.

    The divergence form is the U=1 transcription of sum_mu (A_mu(x) - A_mu(x-e_mu)),
    componentwise on the su(2) basis. It is not Lean's R D^* and not genForm.
    """
    from scipy.linalg import expm

    out = []
    for mode in ("touch", "in"):
        Omega = slab_mask(N, width)
        rng = np.random.default_rng(seed)
        n_bonds = 3 * N ** 3
        coeff = rng.uniform(-eps, eps, size=(n_bonds, 3))
        U = np.stack([expm(coeff[b, 0] * T1 + coeff[b, 1] * T2 + coeff[b, 2] * T3) for b in range(n_bonds)])
        plaquettes = select(all_plaquettes(N), Omega, N, mode)

        def Q_of(p, comps):
            es = edges_of(*p, N)
            ids = [bond_id(e[0], e[1], N) for e in es]
            Um = [U[i] for i in ids]
            A = [comps[i, 0] * T1 + comps[i, 1] * T2 + comps[i, 2] * T3 for i in range(4)]
            cmat = A[0] + Um[0] @ A[1] @ Um[0].conj().T - Um[3] @ A[2] @ Um[3].conj().T - A[3]
            hs = hs_mat(cmat)
            Hhol = Um[0] @ Um[1] @ Um[2].conj().T @ Um[3].conj().T
            re = 0.5 * (Hhol + Hhol.conj().T)
            im = (1.0 / (2j)) * (Hhol - Hhol.conj().T)
            ic = 1j * cmat
            first = float(np.trace(ic @ ic @ (re - I2)).real)
            AZW = -(Um[3] @ A[2] @ Um[3].conj().T)
            AWX = -A[3]
            AXY = A[0]
            AYZ = Um[0] @ A[1] @ Um[0].conj().T
            bs = [1j * M for M in (AZW, AWX, AXY, AYZ)]
            second = 0.0
            for i, j in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
                second += float(np.trace((1j * bs[i]) @ bs[j] @ im).real - np.trace((1j * bs[j]) @ bs[i] @ im).real)
            return hs + 0.5 * (first + second)

        dim = 3 * n_bonds
        H = np.zeros((dim, dim))
        eye = np.eye(12)
        for p in plaquettes:
            es = edges_of(*p, N)
            ids = [bond_id(e[0], e[1], N) for e in es]
            local = np.zeros((12, 12))
            diag = np.zeros(12)
            for a in range(12):
                diag[a] = Q_of(p, eye[a].reshape(4, 3))
                local[a, a] = diag[a]
            for a in range(12):
                for b in range(a + 1, 12):
                    q = Q_of(p, (eye[a] + eye[b]).reshape(4, 3))
                    local[a, b] = local[b, a] = 0.5 * (q - diag[a] - diag[b])
            gids = [3 * b + c for b in ids for c in range(3)]
            for a in range(12):
                for b in range(12):
                    H[gids[a], gids[b]] += local[a, b]
        G = np.zeros((dim, dim))
        for x0 in range(N):
            for x1 in range(N):
                for x2 in range(N):
                    x = (x0, x1, x2)
                    for comp in range(3):
                        terms = []
                        for mu in range(3):
                            bf = bond_id(x, mu, N)
                            xb = list(x)
                            xb[mu] = (xb[mu] - 1) % N
                            bb = bond_id(tuple(xb), mu, N)
                            terms.append((3 * bf + comp, 1.0))
                            terms.append((3 * bb + comp, -1.0))
                        for i, ci in terms:
                            for j, cj in terms:
                                G[i, j] += ci * cj
        raw = spectrum_stats(H)
        pen = spectrum_stats(H + lam * G)
        out.append({"mode": mode, "eps": float(eps), "lambda": float(lam), "raw": raw, "penalised": pen})
    return out



def main():
    t0 = time.time()
    rng = np.random.default_rng(0)
    tests = unit_tests()
    report = {"unit_tests_ok": True, "unit_tests": tests, "families": []}

    # --- geometry and the old counterexample, several tori ---
    geometries = []
    for N, width, label in (
        (4, 2, "slab_N4_W2"),
        (6, 2, "slab_N6_W2"),
        (6, 4, "slab_N6_W4"),
        (8, 2, "slab_N8_W2"),
        (8, 4, "cube_compare"),
    ):
        if label == "cube_compare":
            Omega = cube_mask(N, 2)
        else:
            Omega = slab_mask(N, width)
        plaquettes = all_plaquettes(N)
        geo = rewrite_obstruction(N, Omega, plaquettes)
        touch, both, read, far = bond_sets(N, Omega, plaquettes)
        # phases of U_theta sit on Zb = far. Which of those are ReadBonds?
        read_and_far = len(read & far)
        touch_and_far = len(touch & far)
        geo.update(
            {
                "label": label,
                "N": N,
                "width": width if label != "cube_compare" else None,
                "n_omega": len(Omega),
                "n_touch_bonds": len(touch),
                "n_both_bonds": len(both),
                "n_read_bonds": len(read),
                "n_far_bonds": len(far),
                "read_intersect_far": read_and_far,
                "touch_intersect_far": touch_and_far,
                "proper_nonempty": 0 < len(Omega) < N ** 3,
            }
        )
        if label != "cube_compare":
            ray = {}
            # full spectrum only on N<=6; N=8 Rayleigh only
            for theta, name in ((np.pi, "pi"), (np.pi / 2, "pi_over_2"), (np.pi / 4, "pi_over_4"), (0.0, "zero")):
                r = four_plaquette_rayleigh(N, width, theta)
                entry = {"theta": name, "rayleigh": r}
                if N <= 6 and name in ("pi", "pi_over_2", "zero"):
                    ph = phases_uth(N, Omega, theta)
                    chosen = select(plaquettes, Omega, N, "touch")
                    H = cartan_hessian(N, chosen, ph)
                    entry["touch_spectrum"] = spectrum_stats(H)
                    Hin = cartan_hessian(N, select(plaquettes, Omega, N, "in"), ph)
                    entry["in_spectrum_min"] = spectrum_stats(Hin)["min"]
                ray[name] = entry
            geo["uth"] = ray
            assert ray["pi"]["rayleigh"]["ok"]
        geometries.append(geo)
        print(label, "rewrite_impossible", geo["rewrite_impossible"], "read∩far", read_and_far, "touch∩far", touch_and_far)

    report["geometries"] = geometries

    # --- single-bond Rayleigh minimisation under the shell bounds ---
    shells = []
    for theta_max, delta_max, tag in (
        (np.pi, np.pi, "no_bound_like_frozen_class"),
        (np.pi / 2, np.pi / 2, "half_pi"),
        (np.pi / 4, np.pi / 4, "quarter_pi"),
        (np.pi / 8, np.pi / 8, "eighth_pi"),
        (0.5, 0.5, "half_radian"),
        (np.pi / (2 * np.sqrt(2)), np.pi / (2 * np.sqrt(2)), "a0_equals_phase_cap"),
    ):
        shells.append(
            {
                "tag": tag,
                "theta_max": float(theta_max),
                "delta_max": float(delta_max),
                **max_curl_under_bounds(theta_max, delta_max, trials=400, rng=rng),
            }
        )
    report["single_bond_shell_search"] = shells

    # --- Cartan spectra for a structured plaquette flux inside / outside the bound ---
    N, width = 6, 2
    Omega = slab_mask(N, width)
    plaquettes = all_plaquettes(N)
    touch_ps = select(plaquettes, Omega, N, "touch")
    # pick the outward plaquette P1 at the exit site, dirs (0,1)
    x = exit_site(N, width)
    # phases: set the four edges of that one plaquette, others 0
    structured = []
    for theta_max, phi_target, tag in (
        (np.pi / 2, np.pi, "edges_pi_over_4_holonomy_pi"),
        (np.pi / 4, np.pi, "at_quarter_cap"),
        (np.pi / 8, np.pi / 2, "at_eighth_cap"),
    ):
        ph = np.zeros(3 * N ** 3)
        # phi = t + t - (-t) - (-t) = 4t, so t = phi/4, clipped
        t = min(theta_max, phi_target / 4.0)
        es = edges_of(x, 0, 1, N)
        # (x,0)=+t, (x+e0,1)=+t, (x+e1,0)=-t, (x,1)=-t
        signs = (1.0, 1.0, -1.0, -1.0)
        for e, s in zip(es, signs):
            ph[bond_id(e[0], e[1], N)] = s * t
        H = cartan_hessian(N, touch_ps, ph)
        # also the pure curl test field on those four bonds
        a = np.zeros(3 * N ** 3)
        for e, s in zip(es, (1.0, 1.0, -1.0, -1.0)):
            a[bond_id(e[0], e[1], N)] = s
        q = float(a @ H @ a)
        st = spectrum_stats(H)
        # gradient violation: parallel difference of the two mu-edges is 2t
        structured.append(
            {
                "tag": tag,
                "t": float(t),
                "phi": float(4 * t),
                "parallel_gap": float(2 * t),
                "curl_mode_Q": q,
                "spectrum": st,
                "inside_pointwise": True,
                "inside_gradient_delta_eq_theta_max": bool(2 * t <= theta_max + 1e-12),
            }
        )
    report["structured_flux_N6"] = structured

    # random Cartan configurations on ReadBonds only, N=6, several caps
    random_rows = []
    read = bond_sets(N, Omega, plaquettes)[2]
    read_ids = [bond_id(b[0], b[1], N) for b in read]
    for theta_max, ntry in ((np.pi / 2, 8), (np.pi / 4, 8), (np.pi / 8, 6), (0.3, 6)):
        mins = []
        nnegs = []
        for _ in range(ntry):
            ph = np.zeros(3 * N ** 3)
            ph[read_ids] = rng.uniform(-theta_max, theta_max, size=len(read_ids))
            # reject nothing: pointwise ball. Gradient is whatever the sample has.
            H = cartan_hessian(N, touch_ps, ph)
            st = spectrum_stats(H)
            mins.append(st["min"])
            nnegs.append(st["n_neg"])
        random_rows.append(
            {
                "theta_max": float(theta_max),
                "trials": ntry,
                "min_of_mins": float(np.min(mins)),
                "max_of_mins": float(np.max(mins)),
                "any_negative": bool(np.any(np.array(nnegs) > 0)),
            }
        )
    report["random_cartan_N6"] = random_rows

    # --- non-abelian spot check, N=4 slab width 2 ---
    # Raw Delta is indefinite for a small random shell, and the frozen plaqIn
    # selection is indefinite on the same links. A flat divergence penalty does
    # not remove every negative direction. This is evidence about raw Delta,
    # not about genForm. See SPEC.md.
    print("nonabelian", flush=True)
    Omega4 = slab_mask(4, 2)
    nab = []
    for eps in (0.0, 0.05, 0.2):
        stt = nonabelian_min_eig(4, Omega4, eps, rng, mode="touch")
        nab.append(stt)
        print(" eps", eps, "min", stt["min"], "n_neg", stt["n_neg"], flush=True)
    report["nonabelian_N4_touch"] = nab
    report["gauge_penalty_N4"] = gauge_penalty_compare(0.05)
    print("penalty", report["gauge_penalty_N4"], flush=True)

    # flat control: touching vs inside at U=1 should both be PSD
    H_flat = cartan_hessian(4, select(all_plaquettes(4), Omega4, 4, "touch"), np.zeros(3 * 64))
    report["cartan_flat_N4_touch"] = spectrum_stats(H_flat)

    report["seconds"] = time.time() - t0
    # constants used in the prose
    report["constants"] = {
        "frob_of_diag_1_m1": float(np.sqrt(2)),
        "phase_bound": "|theta| < a0 / (sqrt(2) * ell^j) at level j, from frobNorm(A)=sqrt(2)|theta|/eta and eta cancelling",
        "difference_bound": "|Delta theta| < a0 / (sqrt(2) * ell^(2j))",
        "phi_bound_from_gradient": "|phi| <= 2 |Delta theta|",
        "a0_for_cartan_cos_nonneg_at_j0": float(np.pi / (2 * np.sqrt(2))),
        "note": "These thresholds are model calculations for the eta-free Cartan quadratic form of Delta. They are not a value of gamma_0 and not a Lean theorem.",
    }
    out = "/home/sebastian/BalabanCoercivityLemma/AHP/fidelity/s1-touching/numerics/results.json"
    def _jsonify(o):
        if isinstance(o, dict):
            return {str(k): _jsonify(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)):
            return [_jsonify(v) for v in o]
        if isinstance(o, np.ndarray):
            return _jsonify(o.tolist())
        if isinstance(o, np.generic):
            return o.item()
        return o

    with open(out, "w") as f:
        json.dump(_jsonify(report), f, indent=2)
    print("wrote", out, "in", report["seconds"], "s")


if __name__ == "__main__":
    main()
