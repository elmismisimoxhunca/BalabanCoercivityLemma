#!/usr/bin/env python3
"""
Probe of the exterior-path pencil, on the one operator the frozen path identity
says actually moves.

Transcribed (not the whole Ginv):
  curlValueCovariant          CovariantOperators.lean:315
  periodicPlaquetteHolonomy   ClayStatement.lean:1286
  RMap = U X U^H              CovariantOperators.lean:247, RMap_coe_apply
  hsInner = -1/2 Re Tr(XY)    SuTwoInner.lean:104
  reHolonomy, imHolonomy      DeltaPrime.lean:125, :133
  a1..a4                      DeltaPrimeOperator.lean:287-330
  firstBilPlaq, pairBil,
  secondBilPlaq, bilPlaq      DeltaPrimeOperator.lean:376, :363, :386, :395
  deltaPrimeBilNormLoc
    = (1/2) • ((1/2) • (raw+flip))
                              ZLocOps.lean:119
  inner_deltaKLocCLM
    = ⟨χ curl, χ curl⟩ + deltaPrimeBilL2NormLoc
                              ZLocOps.lean:186
  Uth, Zb                     D1Path.lean:46, :25
  Ginv_lit_path shift
    Δ(t) - Δ(0)               DrPath1.lean:47

NOT transcribed, and not claimed: Wop, Mass, Tfull, Q, H, C2, Delta2, Ginv, G1inv.
Delta2's form is 2⟨H C2(A), J⟩ (R2Algebra.lean:220). This script never builds it.
A numerical hit is evidence about Δ, not a theorem about P428Target8SG.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent / "probe_results.json"

# Orthonormal su(2) basis for hsInner. hs(Ea,Eb)=δ_ab.
E = [
    np.array([[1j, 0], [0, -1j]], dtype=np.complex128),
    np.array([[0, 1], [-1, 0]], dtype=np.complex128),
    np.array([[0, 1j], [1j, 0]], dtype=np.complex128),
]
I2 = np.eye(2, dtype=np.complex128)
Z2 = np.zeros((2, 2), dtype=np.complex128)


def hs(X, Y) -> float:
    """SuTwoInner.lean:104."""
    return float(-0.5 * np.trace(X @ Y).real)


def rmap(U, X):
    """CovariantOperators.lean RMap_coe_apply."""
    return U @ X @ U.conj().T


def u_theta(theta: float) -> np.ndarray:
    """D1Path.lean uMat: diag(e^{iθ}, e^{-iθ})."""
    z = np.exp(1j * theta)
    return np.array([[z, 0], [0, z.conjugate()]], dtype=np.complex128)


def check_basis():
    G = np.array([[hs(E[i], E[j]) for j in range(3)] for i in range(3)])
    assert np.allclose(G, np.eye(3), atol=1e-12), G


def coords_of(X) -> np.ndarray:
    return np.array([hs(Ea, X) for Ea in E])


class Lattice:
    def __init__(self, N: int, box: int):
        assert 2 <= box < N <= 8
        self.N = N
        self.box = box
        self.sites = [(x, y, z) for x in range(N) for y in range(N) for z in range(N)]
        self.site_index = {s: i for i, s in enumerate(self.sites)}
        self.bonds = [(s, mu) for s in self.sites for mu in range(3)]
        self.bond_index = {b: i for i, b in enumerate(self.bonds)}
        self.plaquettes = []
        for s in self.sites:
            for mu, nu in ((0, 1), (0, 2), (1, 2)):
                self.plaquettes.append((s, mu, nu))
        self.nB = len(self.bonds)
        self.nP = len(self.plaquettes)
        self.dim = self.nB * 3  # bond × su(2)
        self.both = []
        self.zb = []
        self.shell = []
        for b in self.bonds:
            x, mu = b
            y = self.shift(x, mu)
            inn = self.in_om(x)
            iny = self.in_om(y)
            if inn and iny:
                self.both.append(b)
            elif (not inn) and (not iny):
                self.zb.append(b)
            else:
                self.shell.append(b)
        self.plaq_in = []
        for p in self.plaquettes:
            if self.corners_in(p):
                self.plaq_in.append(p)

    def shift(self, x, mu):
        y = list(x)
        y[mu] = (y[mu] + 1) % self.N
        return tuple(y)

    def in_om(self, x) -> bool:
        return all(c < self.box for c in x)

    def corners_in(self, p) -> bool:
        """plaqIn: all four boundary bonds have both ends in Ω0 (ZR2Ops2.lean:74)."""
        x, mu, nu = p
        corners = [
            x,
            self.shift(x, mu),
            self.shift(x, nu),
            self.shift(self.shift(x, mu), nu),
        ]
        return all(self.in_om(c) for c in corners)

    def edges_of(self, p):
        x, mu, nu = p
        return [
            (x, mu),
            (self.shift(x, mu), nu),
            (self.shift(x, nu), mu),
            (x, nu),
        ]

    def holonomy(self, U, p):
        """ClayStatement.lean:1286. U(x,μ) U(x+μ,ν) U(x+ν,μ)^{-1} U(x,ν)^{-1}."""
        x, mu, nu = p
        e1 = (x, mu)
        e2 = (self.shift(x, mu), nu)
        e3 = (self.shift(x, nu), mu)
        e4 = (x, nu)
        return U[e1] @ U[e2] @ U[e3].conj().T @ U[e4].conj().T

    def config(self, theta: float, eps: float, rng=None, random_exterior: bool = False):
        """Exterior-only path: identity off Zb, u_θ on Zb (D1Path.lean:46),
        plus a fixed interior flux u_ε on BothIn direction-0 bonds.
        The interior flux is NOT part of Uth; it is frozen along θ so the path
        stays exterior-only (bonds outside Zb do not move with θ)."""
        U = {}
        ut = u_theta(theta)
        ue = u_theta(eps)
        for b in self.bonds:
            if b in self._zb_set and random_exterior:
                U[b] = random_su2(rng)
            elif b in self._zb_set:
                U[b] = ut
            elif self.interior_mode == "one" and b == self.interior_bond:
                # one BothIn bond, so parallel edges do not cancel the plaquette holonomy
                U[b] = ue
            elif self.interior_mode == "uniform" and b in self._both_set and b[1] == 0:
                # every BothIn direction-0 bond. Parallel edges cancel, plaqIn holonomy stays 1.
                U[b] = ue
            else:
                U[b] = I2.copy()
        return U

    def _cache_sets(self):
        self._zb_set = set(self.zb)
        self._both_set = set(self.both)
        if not hasattr(self, "interior_mode"):
            self.interior_mode = "one"
        if not hasattr(self, "interior_bond"):
            self.interior_bond = next(b for b in self.both if b[1] == 0)

    def curl_matrix(self, U) -> np.ndarray:
        """Rows: plaquette × su(2). Cols: bond × su(2).
        curlValueCovariant, CovariantOperators.lean:315.
        Coefficients via hsInner, basis ON, so C^T C is the D* χ D form."""
        C = np.zeros((self.nP * 3, self.dim), dtype=np.float64)
        for ip, p in enumerate(self.plaquettes):
            x, mu, nu = p
            # four contributions: +A(x,μ), +R(U(x,μ)) A(x+μ,ν),
            # -R(U(x,ν)) A(x+ν,μ), -A(x,ν)
            terms = [
                ((x, mu), I2, +1.0),
                ((self.shift(x, mu), nu), U[(x, mu)], +1.0),
                ((self.shift(x, nu), mu), U[(x, nu)], -1.0),
                ((x, nu), I2, -1.0),
            ]
            for bond, transport, sign in terms:
                ib = self.bond_index[bond]
                for s in range(3):
                    contrib = sign * (E[s] if transport is I2 else rmap(transport, E[s]))
                    # transport is a matrix; I2 identity means R(1)=id, but the first
                    # and last terms are unconjugated (the definition adds A, not R(U)A).
                    coef = coords_of(contrib)
                    col = ib * 3 + s
                    C[ip * 3 : ip * 3 + 3, col] += coef
        return C

    def delta_prime_matrix(self, U, which: str) -> np.ndarray:
        """Normalized Δ' on the selected plaquettes.
        which: 'all' or 'in' (plaqIn Ω0)."""
        M = np.zeros((self.dim, self.dim), dtype=np.float64)
        plaquettes = self.plaquettes if which == "all" else self.plaq_in
        for p in plaquettes:
            bonds = self.edges_of(p)
            re, im = self._re_im(U, p)
            # 12 local basis vectors
            local = [(ib, s) for ib in range(4) for s in range(3)]
            gram = np.zeros((12, 12), dtype=np.float64)
            fields = []
            for ib, s in local:
                A = {bonds[k]: Z2.copy() for k in range(4)}
                A[bonds[ib]] = E[s].copy()
                fields.append(A)
            for i in range(12):
                for j in range(i, 12):
                    raw_ij = self._bil_plaq(U, p, fields[i], fields[j], re, im)
                    raw_ji = raw_ij if i == j else self._bil_plaq(U, p, fields[j], fields[i], re, im)
                    # ZLocOps.lean:119, (1/4)(raw+flip)
                    val = 0.25 * (raw_ij + raw_ji)
                    gram[i, j] = val
                    gram[j, i] = val
            for i, (ib, s) in enumerate(local):
                ci = self.bond_index[bonds[ib]] * 3 + s
                for j, (jb, t) in enumerate(local):
                    cj = self.bond_index[bonds[jb]] * 3 + t
                    M[ci, cj] += gram[i, j]
        return M

    def _re_im(self, U, p):
        H = self.holonomy(U, p)
        Hinv = H.conj().T
        re = 0.5 * (H + Hinv)
        im = (1 / (2j)) * (H - Hinv)
        return re, im

    def _a_of(self, U, p, A):
        """a1..a4, DeltaPrimeOperator.lean:287-330. Missing bonds read as 0."""
        x, mu, nu = p
        def Av(b):
            return A.get(b, Z2)
        a1 = -rmap(U[(x, nu)], Av((self.shift(x, nu), mu)))
        a2 = -Av((x, nu))
        a3 = Av((x, mu))
        a4 = rmap(U[(x, mu)], Av((self.shift(x, mu), nu)))
        return a1, a2, a3, a4

    def _curl_of(self, U, p, A):
        x, mu, nu = p
        def Av(b):
            return A.get(b, Z2)
        return (
            Av((x, mu))
            + rmap(U[(x, mu)], Av((self.shift(x, mu), nu)))
            - rmap(U[(x, nu)], Av((self.shift(x, nu), mu)))
            - Av((x, nu))
        )

    def _bil_plaq(self, U, p, A, B, re, im) -> float:
        """bilPlaq = firstBilPlaq + secondBilPlaq, raw trace (not yet normalized)."""
        cA = self._curl_of(U, p, A)
        cB = self._curl_of(U, p, B)
        first = np.trace((1j * cA) @ (1j * cB) @ (re - I2)).real
        a1A, a2A, a3A, a4A = self._a_of(U, p, A)
        a1B, a2B, a3B, a4B = self._a_of(U, p, B)
        bA = [1j * a1A, 1j * a2A, 1j * a3A, 1j * a4A]
        bB = [1j * a1B, 1j * a2B, 1j * a3B, 1j * a4B]
        pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
        second = 0.0
        for i, j in pairs:
            fA = bA[i]
            gB = bB[j]
            second += np.trace((1j * fA) @ gB @ im).real - np.trace((1j * gB) @ fA @ im).real
        return float(first + second)

    def delta_matrix(self, U, which: str) -> np.ndarray:
        """deltaKLocCLM quadratic-form matrix, ZLocOps.lean:181 and :186.
        which='all' is Set.univ; which='in' is plaqIn Ω0."""
        mask = None
        if which == "in":
            # zero rows of plaquettes outside plaqIn, equivalent to χ_P
            keep = set(id(p) for p in self.plaq_in)  # unused; index set below
        C = self.curl_matrix(U)
        if which == "in":
            rows = np.zeros(self.nP, dtype=bool)
            pin = set(self.plaq_in)
            for ip, p in enumerate(self.plaquettes):
                rows[ip] = p in pin
            # p in pin works if tuples
            row_mask = np.repeat(rows, 3)
            C = C * row_mask[:, None]
        DD = C.T @ C
        DP = self.delta_prime_matrix(U, which)
        return DD + DP

    def im_hol_energy(self, U) -> dict:
        """Scale of Im U(∂p) on plaqIn, the input of JSU2Loc (ZLocJ.lean:71).
        Not J itself (no D*)."""
        acc = 0.0
        mx = 0.0
        for p in self.plaq_in:
            _, im = self._re_im(U, p)
            nrm = float(np.linalg.norm(im))
            acc += nrm
            mx = max(mx, nrm)
        return {"sum_frob_im_plaqIn": acc, "max_frob_im_plaqIn": mx, "n_plaqIn": len(self.plaq_in)}


def random_su2(rng: np.random.Generator) -> np.ndarray:
    """Haar SU(2) via quaternion Gaussians."""
    q = rng.normal(size=4)
    q = q / np.linalg.norm(q)
    a, b, c, d = q
    return np.array(
        [[a + 1j * b, c + 1j * d], [-(c - 1j * d), a - 1j * b]],
        dtype=np.complex128,
    )


def sym_err(M) -> float:
    return float(np.max(np.abs(M - M.T)))


def spectrum_report(M, ker_cut: float = 1e-7) -> dict:
    ev = np.linalg.eigvalsh(M)
    n_neg = int(np.sum(ev < -1e-7))
    n_zero = int(np.sum(np.abs(ev) <= ker_cut))
    pos = ev[ev > ker_cut]
    return {
        "min": float(ev[0]),
        "max": float(ev[-1]),
        "n_neg": n_neg,
        "n_abs_le_cut": n_zero,
        "smallest_positive": float(pos[0]) if len(pos) else None,
        "cond_on_pos": float(pos[-1] / pos[0]) if len(pos) else None,
    }


def compression_gap(M, V) -> dict:
    """Eigenvalues of V^T M V, V orthonormal columns = flat positive subspace."""
    R = V.T @ M @ V
    R = 0.5 * (R + R.T)
    ev = np.linalg.eigvalsh(R)
    return {
        "min": float(ev[0]),
        "max": float(ev[-1]),
        "n_neg": int(np.sum(ev < -1e-7)),
        "n_abs_le_1e-6": int(np.sum(np.abs(ev) <= 1e-6)),
        "min_abs": float(np.min(np.abs(ev))),
    }


def run_lattice(N: int, box: int, thetas, eps_list, n_random: int, seed: int) -> dict:
    t0 = time.time()
    lat = Lattice(N, box)
    lat._cache_sets()
    print(
        f"N={N} box={box} dim={lat.dim} bonds={lat.nB} both={len(lat.both)} "
        f"zb={len(lat.zb)} shell={len(lat.shell)} plaqIn={len(lat.plaq_in)}",
        flush=True,
    )
    U0 = lat.config(0.0, 0.0)
    D0 = lat.delta_matrix(U0, "all")
    assert sym_err(D0) < 1e-8, sym_err(D0)
    # Δ' at U=1 must vanish (re-1=0, im=0).
    DP0 = lat.delta_prime_matrix(U0, "all")
    dp0 = float(np.max(np.abs(DP0)))
    ev0 = np.linalg.eigvalsh(D0)
    ker = int(np.sum(np.abs(ev0) <= 1e-7))
    # expected abelian kernel: gradients of site su(2) fields, dim 3*(N^3-1),
    # plus harmonic H^1(T^3) ⊗ su(2), dim 9. Total 3 N^3 + 6.
    expected_ker = 3 * (N**3) + 6
    Vpos = np.linalg.eigh(D0)[1][:, ev0 > 1e-6]
    print(
        f"  flat kernel {ker} (abelian guess {expected_ker}) "
        f"Δ'max {dp0:.2e} pos-subspace {Vpos.shape[1]} sym {sym_err(D0):.2e}",
        flush=True,
    )

    # gradient check: curl of a gradient at U=1 is 0, so Δ(grad)=0
    lam = np.zeros((N**3, 3), dtype=np.float64)
    lam[0, 0] = 1.0
    grad = np.zeros(lat.dim)
    for b in lat.bonds:
        x, mu = b
        y = lat.shift(x, mu)
        ib = lat.bond_index[b]
        # (grad λ)(b) = λ(y) - λ(x) at U=1, in su(2) components
        grad[ib * 3 : ib * 3 + 3] = lam[lat.site_index[y]] - lam[lat.site_index[x]]
    grad_form = float(grad @ D0 @ grad)
    print(f"  ⟨grad, Δ grad⟩ at flat = {grad_form:.2e}", flush=True)

    rows = []
    separation = []
    for eps in eps_list:
        Ueps = lat.config(0.0, eps)
        Deps = lat.delta_matrix(Ueps, "all")
        Dfd = Deps - D0  # interior response of Δ at θ=0; NOT Delta2
        imE = lat.im_hol_energy(Ueps)
        # B is the interior response compressed later
        for th in thetas:
            U = lat.config(th, eps)
            M = lat.delta_matrix(U, "all")
            # shift cited by Ginv_lit_path: Δ(t)-Δ(0) at fixed interior
            shift = M - Deps
            spec = spectrum_report(M)
            comp = compression_gap(M, Vpos)
            comp_shift = compression_gap(shift, Vpos)
            # probe pencil on the flat positive subspace:
            # carrier = compression of Δ(θ), correction = compression of Dfd
            # (a stand-in, not Delta2). Ask whether carrier stays invertible
            # while carrier - Dfd does not.
            Mc = 0.5 * (Vpos.T @ M @ Vpos + (Vpos.T @ M @ Vpos).T)
            Dc = 0.5 * (Vpos.T @ Dfd @ Vpos + (Vpos.T @ Dfd @ Vpos).T)
            evM = np.linalg.eigvalsh(Mc)
            evP = np.linalg.eigvalsh(Mc - Dc)
            hit = bool(np.min(np.abs(evM)) > 1e-6 and (np.min(np.abs(evP)) <= 1e-6 or np.min(evP) < -1e-7))
            # also: carrier PD but pencil indefinite
            hit_indef = bool(np.min(evM) > 1e-6 and np.min(evP) < -1e-7)
            row = {
                "eps": eps,
                "theta": th,
                "delta_min": spec["min"],
                "delta_n_neg": spec["n_neg"],
                "delta_n_small": spec["n_abs_le_cut"],
                "comp_min": comp["min"],
                "comp_min_abs": comp["min_abs"],
                "comp_n_neg": comp["n_neg"],
                "shift_comp_min": comp_shift["min"],
                "pencil_min": float(np.min(evP)),
                "carrier_min": float(np.min(evM)),
                "hit_singular_or_indef": hit,
                "hit_indef_while_carrier_pd": hit_indef,
            }
            rows.append(row)
            if hit or hit_indef:
                separation.append(row)
            print(
                f"  eps={eps:.3f} θ={th:.3f} Δmin={spec['min']:.4e} "
                f"comp={comp['min']:.4e} shift={comp_shift['min']:.4e} "
                f"pen={np.min(evP):.4e} hit={hit}",
                flush=True,
            )
        print(f"  im-hol at eps={eps}: {imE}", flush=True)

    # random exterior, interior flat (eps=0) and one curved interior
    rng = np.random.default_rng(seed)
    random_rows = []
    worst = None
    for eps in (0.0, 0.15):
        Ueps = lat.config(0.0, eps)
        Deps = lat.delta_matrix(Ueps, "all")
        Dfd = Deps - D0
        neg_count = 0
        small_gap = 0
        min_comp = 1e99
        min_pen = 1e99
        hits = 0
        for s in range(n_random):
            U = lat.config(0.0, eps, rng=rng, random_exterior=True)
            M = lat.delta_matrix(U, "all")
            comp = compression_gap(M, Vpos)
            Mc = 0.5 * (Vpos.T @ M @ Vpos + (Vpos.T @ M @ Vpos).T)
            Dc = 0.5 * (Vpos.T @ Dfd @ Vpos + (Vpos.T @ Dfd @ Vpos).T)
            evM = np.linalg.eigvalsh(Mc)
            evP = np.linalg.eigvalsh(Mc - Dc)
            if comp["min"] < -1e-7:
                neg_count += 1
            if comp["min_abs"] < 1e-3:
                small_gap += 1
            min_comp = min(min_comp, comp["min"])
            min_pen = min(min_pen, float(np.min(evP)))
            if np.min(np.abs(evM)) > 1e-6 and np.min(evP) < -1e-7:
                hits += 1
            if worst is None or comp["min"] < worst["comp_min"]:
                worst = {"eps": eps, "sample": s, "comp_min": comp["min"], "comp_min_abs": comp["min_abs"],
                         "pencil_min": float(np.min(evP)), "carrier_min": float(np.min(evM))}
        random_rows.append({
            "eps": eps,
            "n": n_random,
            "n_comp_negative": neg_count,
            "n_comp_gap_below_1e-3": small_gap,
            "min_comp": min_comp,
            "min_pencil": min_pen,
            "n_pencil_neg_while_carrier_nonsing": hits,
        })
        print(f"  random eps={eps}: {random_rows[-1]}", flush=True)

    # alignment: at the θ where compression of the shift is most negative,
    # matrix element of Dfd on that near-min vector.
    align = []
    for eps in eps_list:
        if eps == 0.0:
            continue
        Ueps = lat.config(0.0, eps)
        Deps = lat.delta_matrix(Ueps, "all")
        Dfd = Deps - D0
        Dc = 0.5 * (Vpos.T @ Dfd @ Vpos + (Vpos.T @ Dfd @ Vpos).T)
        best = None
        for th in thetas:
            U = lat.config(th, eps)
            M = lat.delta_matrix(U, "all")
            shift = M - Deps
            Sc = 0.5 * (Vpos.T @ shift @ Vpos + (Vpos.T @ shift @ Vpos).T)
            ev, evec = np.linalg.eigh(Sc)
            v = evec[:, 0]
            quad_D = float(v @ Dc @ v)
            rec = {"eps": eps, "theta": th, "shift_min": float(ev[0]), "v_D_v": quad_D,
                   "D_opnorm": float(np.linalg.norm(Dc, 2))}
            if best is None or rec["shift_min"] < best["shift_min"]:
                best = rec
        align.append(best)
        print(f"  align {best}", flush=True)

    out = {
        "N": N,
        "box": box,
        "dim": lat.dim,
        "n_both": len(lat.both),
        "n_zb": len(lat.zb),
        "n_shell": len(lat.shell),
        "n_plaqIn": len(lat.plaq_in),
        "flat_kernel": ker,
        "abelian_kernel_guess": expected_ker,
        "delta_prime_flat_max": dp0,
        "grad_form_flat": grad_form,
        "pos_dim": int(Vpos.shape[1]),
        "grid": rows,
        "separation_hits": separation,
        "random": random_rows,
        "worst_random": worst,
        "alignment": align,
        "seconds": time.time() - t0,
    }
    return out


def main():
    check_basis()
    # side at most 8; N=4 is 576-dimensional. N=3 first as a check, then N=4.
    thetas = [k * np.pi / 8 for k in range(0, 17)]
    eps_list = [0.0, 0.05, 0.2]
    results = []
    results.append(run_lattice(3, 2, thetas, eps_list, n_random=12, seed=1))
    results.append(run_lattice(4, 2, thetas, [0.0, 0.05, 0.2], n_random=8, seed=2))
    payload = {"results": results, "note": "evidence about deltaK only; not Ginv; not a theorem"}
    OUT.write_text(json.dumps(payload, indent=2))
    print("wrote", OUT, flush=True)


if __name__ == "__main__":
    main()
