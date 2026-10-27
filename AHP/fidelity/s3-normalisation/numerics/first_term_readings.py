#!/usr/bin/env python3
"""Scalar normalisation model for the frozen first term of (3.156).

Evidence only. Not a theorem. Not the SU(2) covariant operators.

Every matrix below is either a transcribed weight or a labelled stand-in.

Transcribed weights (Lean line = the formula this script copies):
  eta            = ell**(-k)
                   ZXR2Wire2.lean:37  `eta := ((P.ell : ℝ) ^ P.k)⁻¹`
  Q_j            = ell**(-j) * Qlin_j
                   ZXR2Sector.lean:100 `(ell ^ j)⁻¹ • QlinB` (def QfullOf at :97)
  C_lane_j       = ell**(-j) * raw_j
                   ZXR2Sector.lean:111 `(ell ^ j)⁻¹ • C2rawB` (def C2fullOf at :109)
  mass weight_j  = a * ell**j
                   ZXR2Ops3.lean:99    `a * (G.ell : ℝ) ^ j`   (d = 3; def massW at :98)
  Mass form      = sum_j weight_j * ||Q_j A||^2
                   ZXR2Ops3.lean:112   inner_MassFull
  Quad           = Quad0 + Mass
                   R2Algebra.lean:145  Ginv = Dpi + Ts∘T + Mass
                   Quad0 is a stand-in for Dpi + Ts∘T, not gradCovariant.
  G              = Quad⁻¹
                   R2Algebra.lean:147
  H              = G Q* (Q G Q*)⁻¹
                   R2Algebra.lean:149-150
  K(A)           = <A, Quad A> - 2 <H(C A), J>
                   R2Algebra.lean:153
  N              = Q K⁻¹ Q*
                   ZXG3A.lean:35       Nmat = Q ∘ G1 ∘ Qs
  firstTerm      = eta * <τ* B, N⁻¹ τ* B>
                   ZXG3A.lean:50
  τ* B           = B placed at level k, zero below, no scalar
                   ZXG3A.lean:46-49 and ZGU1D.lean:55,67
                   (tau_adj_apply / tau_adj_norm; FullSupp)
  J              in the fine space, the η = 1 source
                   ZXR2Wire2.lean:51-53  Jf = -(JSU2Loc 1 ...)
                   ZIngredientJ.lean:111 JSU2 carries (η⁻¹)^3

Printed readings, level by level. Same Q and same Quad*eta.
H is recomputed; it matches the lane H when Quad is scaled by eta
(checked). The three C assemblies are the three powers:

  plainH     C_j = eta**2 * raw_j
             (3.14) p.393: Q_j(U, ηA) = η Dq·A + η² raw + …
             second order of the left side = η L^{-j} raw = C_j^{(2)}
             p.421 plain H: C^{(2)} = L^j η C_j^{(2)} = η² raw
             At j = k only, lane/print = L^{-k}/η² = η^{-1}.
  draft      C_j = L^{-j} raw     (the stored field)
             (3.11) p.392 weight η^d times J ~ η^{-3}
             (ZIngredientJ.lean:111) cancels at d = 3, so the draft
             pairs the stored C2 with J and does not rescale it.
             Top-level power 1.
  linearEta  C_j = raw_j
             Alternate placement of the single η in (3.14): η sits on
             the linear jet only, the second jet is the η-free raw,
             and plain-H multiplies by L^j η and then cancels it.
             At j = k, lane/print = L^{-k} = η.

(3.136) p.422 weight (L^j η)^{d+1} equals 1 at j = k, so it does not
choose among these three powers at the top level. (3.24) is the site
recursion, not the bond weight in (3.16) or (3.128); a separate check
shows substituting a_j moves the flat first term. (3.156) and (3.157)
display neither η nor τ*.

Quad0, Qlin and raw are stand-ins. The identity under test is about the
weights, so it would have to hold for every full-rank jet, including
these. A ratio that depends on B refutes a universal scalar.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent / "out"


def inv_np(M: np.ndarray) -> np.ndarray:
    return np.linalg.inv(M)


def sym(M: np.ndarray) -> np.ndarray:
    return 0.5 * (M + M.T)


def stack_Q(ell: int, Qlin: list[np.ndarray]) -> np.ndarray:
    """QfullOf weight, ZXR2Sector.lean:100."""
    blocks = [ell ** (-j) * Qlin[j] for j in range(len(Qlin))]
    return np.vstack(blocks)


def mass_matrix(ell: int, a: float, Q: np.ndarray, nB: int) -> np.ndarray:
    """inner_MassFull, ZXR2Ops3.lean:112, weight massW at line 99."""
    nE = Q.shape[1]
    M = np.zeros((nE, nE))
    for j in range(Q.shape[0] // nB):
        Qj = Q[j * nB : (j + 1) * nB]
        M += (a * ell**j) * (Qj.T @ Qj)
    return M


def lam_of(Quad: np.ndarray, Q: np.ndarray, J: np.ndarray) -> np.ndarray:
    """H* J, with H = G Q* (Q G Q*)^{-1}, R2Algebra.lean:147 and :149-150."""
    G = inv_np(Quad)
    N = Q @ G @ Q.T
    H = G @ Q.T @ inv_np(N)
    return H.T @ J


def cross_matrix(lam: np.ndarray, T: list[np.ndarray]) -> np.ndarray:
    """Symmetric operator S_c with <A, S_c A> = 2 <H(C(A)), J>, R2Algebra.lean:153."""
    nE = T[0].shape[-1]
    M = np.zeros((nE, nE))
    offset = 0
    for Tj in T:
        nB = Tj.shape[0]
        for b in range(nB):
            M += lam[offset + b] * Tj[b]
        offset += nB
    return sym(2 * M)


def schur(S: np.ndarray, Q: np.ndarray, f: np.ndarray) -> float:
    """<f, (Q S^{-1} Q*)^{-1} f>, ZXG3A.lean:35 and :50."""
    G1 = inv_np(S)
    N = Q @ G1 @ Q.T
    return float(f @ inv_np(N) @ f)


def tau_star(B: np.ndarray, k: int, nB: int, n_levels: int) -> np.ndarray:
    """Top-level embedding, no scalar. ZXG3A.lean:46-49, ZGU1D.lean:55."""
    f = np.zeros(n_levels * nB)
    f[k * nB : (k + 1) * nB] = B
    return f


def scale_raw(raw: list[np.ndarray], factors: list[float]) -> list[np.ndarray]:
    return [factors[j] * raw[j] for j in range(len(raw))]


def min_eig(M: np.ndarray) -> float:
    return float(np.linalg.eigvalsh(sym(M)).min())


def reading_factors(kind: str, ell: int, k: int) -> list[float]:
    """Multiplier in front of raw_j for each printed C assembly."""
    eta = ell ** (-k)
    out = []
    for j in range(k + 1):
        if kind == "lane":
            out.append(ell ** (-j))
        elif kind == "plainH":
            out.append(eta**2)
        elif kind == "draft":
            out.append(ell ** (-j))
        elif kind == "linearEta":
            out.append(1.0)
        elif kind == "uniformBody":
            # control: printed C = eta * stored C, one global factor
            out.append(eta * ell ** (-j))
        else:
            raise ValueError(kind)
    return out


def run_case(ell: int, k: int, a: float, Qlin, raw, Quad0, J, thetas, Blist, label: str) -> dict:
    eta = ell ** (-k)
    nB = Qlin[0].shape[0]
    n_levels = k + 1
    Q = stack_Q(ell, Qlin)
    Mass = mass_matrix(ell, a, Q, nB)
    Quad = sym(Quad0 + Mass)
    lam = lam_of(Quad, Q, J)
    # H invariance under Quad |-> eta Quad
    lam_scaled = lam_of(eta * Quad, Q, J)
    h_err = float(np.linalg.norm(lam - lam_scaled))

    T_lane_unit = scale_raw(raw, reading_factors("lane", ell, k))
    rows = []
    for theta in thetas:
        T_lane = scale_raw(T_lane_unit, [theta] * n_levels)
        Sc = cross_matrix(lam, T_lane)
        SL = sym(Quad - Sc)
        e_min = min_eig(SL)
        rec = {"theta": theta, "min_eig_lane": e_min, "readings": {}}
        if e_min <= 1e-8:
            rec["skipped"] = "lane K not positive definite"
            rows.append(rec)
            continue
        for kind in ("plainH", "draft", "linearEta", "uniformBody"):
            fac = reading_factors(kind, ell, k)
            T = scale_raw(raw, [theta * f for f in fac])
            ScP = cross_matrix(lam, T)
            SP = sym(eta * Quad - ScP)
            eP = min_eig(SP)
            ratios = []
            values = []
            if eP <= 1e-8:
                rec["readings"][kind] = {"min_eig": eP, "skipped": "print K not PD"}
                continue
            for B in Blist:
                f = tau_star(np.asarray(B, dtype=float), k, nB, n_levels)
                frozen = eta * schur(SL, Q, f)
                printed = schur(SP, Q, f)
                ratios.append(frozen / printed)
                values.append({"frozen": frozen, "printed": printed, "B": list(map(float, B))})
            arr = np.array(ratios)
            rec["readings"][kind] = {
                "min_eig": eP,
                "ratio_min": float(arr.min()),
                "ratio_max": float(arr.max()),
                "ratio_spread": float(arr.max() / arr.min()) if arr.min() != 0 else None,
                "ratios": [float(x) for x in arr],
                "values": values,
            }
        rows.append(rec)
    return {
        "label": label,
        "ell": ell,
        "k": k,
        "eta": eta,
        "a": a,
        "H_invariance_err": h_err,
        "quad_min_eig": min_eig(Quad),
        "rows": rows,
    }


# ----- exact rational witness -----


def inv_frac(A):
    n = len(A)
    M = [list(map(Fraction, row)) + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        if M[piv][col] == 0:
            raise ZeroDivisionError("singular")
        M[col], M[piv] = M[piv], M[col]
        pivv = M[col][col]
        M[col] = [x / pivv for x in M[col]]
        for r in range(n):
            if r == col:
                continue
            fct = M[r][col]
            if fct != 0:
                M[r] = [a - fct * b for a, b in zip(M[r], M[col])]
    return [row[n:] for row in M]


def _mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def _mv(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def _Tp(A):
    return [list(c) for c in zip(*A)]


def _add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def _scl(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def _qf(S, v):
    Sv = _mv(S, v)
    return sum(v[i] * Sv[i] for i in range(len(v)))


def _eye(n):
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def _pd(M):
    """Sylvester: every leading principal minor positive."""
    n = len(M)
    for k in range(1, n + 1):
        A = [list(map(Fraction, row[:k])) for row in M[:k]]
        det = Fraction(1)
        for col in range(k):
            piv = max(range(col, k), key=lambda r: abs(A[r][col]))
            if A[piv][col] == 0:
                return False
            if piv != col:
                A[col], A[piv] = A[piv], A[col]
                det = -det
            det *= A[col][col]
            pv = A[col][col]
            for r in range(col + 1, k):
                fct = A[r][col] / pv
                A[r] = [A[r][j] - fct * A[col][j] for j in range(k)]
        if det <= 0:
            return False
    return True


def _vv(v):
    v = list(map(Fraction, v))
    return [[v[i] * v[j] for j in range(4)] for i in range(4)]


def exact_model(zero_level0: bool):
    """ell = 2, k = 1, eta = 1/2, a = 1, theta = 1/10.

    Four fine coordinates, two bonds at each of two levels. Qlin overlaps.
    J is chosen so H* J = (1,1,1,1), so both levels enter the cross term.
    raw jets are rank-one and not symmetric across the two top bonds.
    """
    ell = 2
    eta = Fraction(1, 2)
    theta = Fraction(1, 10)
    Q0 = [[Fraction(x) for x in row] for row in ([1, 0, 1, 0], [0, 1, 0, 1])]
    Q1 = [[Fraction(x) for x in row] for row in ([1, 1, 0, 0], [0, 1, 1, 0])]
    Q = Q0 + _scl(Fraction(1, 2), Q1)
    Quad = _eye(4)
    for j, Qj in enumerate((Q0, _scl(Fraction(1, 2), Q1))):
        # massW = a * ell^j with a = 1, ZXR2Ops3.lean:99
        Quad = _add(Quad, _scl(Fraction(ell) ** j, _mm(_Tp(Qj), Qj)))
    G = inv_frac(Quad)
    N = _mm(Q, _mm(G, _Tp(Q)))
    # lam = H* J = N^{-1} Q G J. Choose J so lam = (1,1,1,1).
    Mop = _mm(inv_frac(N), _mm(Q, G))
    J = _mv(inv_frac(Mop), [Fraction(1), Fraction(1), Fraction(1), Fraction(1)])
    lam = _mv(Mop, J)
    z = _vv([0, 0, 0, 0])
    raw = [
        [z, z] if zero_level0 else [_vv([1, 0, 0, 0]), _vv([0, 1, 1, 0])],
        [_vv([0, 0, 1, 0]), _vv([1, 0, 1, 1])],
    ]

    def Sc(facs):
        Mtr = [[Fraction(0)] * 4 for _ in range(4)]
        off = 0
        for j, fct in enumerate(facs):
            for b in range(2):
                Mtr = _add(Mtr, _scl(lam[off + b] * theta * fct, raw[j][b]))
            off += 2
        return _scl(2, Mtr)

    fac = {
        "lane": [Fraction(1), Fraction(1, 2)],
        "plainH": [eta ** 2, eta ** 2],
        "draft": [Fraction(1), Fraction(1, 2)],
        "linearEta": [Fraction(1), Fraction(1)],
        "uniformBody": [eta * Fraction(1), eta * Fraction(1, 2)],
    }
    SL = _add(Quad, _scl(-1, Sc(fac["lane"])))
    Bs = [
        [Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(1)],
        [Fraction(1), Fraction(2)],
        [Fraction(3), Fraction(-1)],
    ]
    iL = inv_frac(_mm(Q, _mm(inv_frac(SL), _Tp(Q))))
    kinds = {}
    for name in ("plainH", "draft", "linearEta", "uniformBody"):
        SP = _add(_scl(eta, Quad), _scl(-1, Sc(fac[name])))
        iP = inv_frac(_mm(Q, _mm(inv_frac(SP), _Tp(Q))))
        rows = []
        for B in Bs:
            f = [Fraction(0), Fraction(0), B[0], B[1]]
            frozen = eta * _qf(iL, f)
            printed = _qf(iP, f)
            rows.append(
                {
                    "B": [str(x) for x in B],
                    "frozen": str(frozen),
                    "printed": str(printed),
                    "ratio": str(frozen / printed),
                }
            )
        rats = [Fraction(r["ratio"]) for r in rows]
        kinds[name] = {
            "pd": _pd(SP),
            "rows": rows,
            "all_equal": all(r == rats[0] for r in rats),
            "spread": str(max(rats) / min(rats)),
        }
    return {
        "ell": 2,
        "k": 1,
        "eta": "1/2",
        "a": 1,
        "theta": str(theta),
        "zero_level0_jet": zero_level0,
        "Q0": [[str(x) for x in row] for row in Q0],
        "Q1": [[str(x) for x in row] for row in Q1],
        "J": [str(x) for x in J],
        "lam": [str(x) for x in lam],
        "lane_pd": _pd(SL),
        "kinds": kinds,
    }


def aj_shift_example() -> dict:
    """Flat first term at k = 2 if massW's constant a is replaced by (3.24)'s a_j.

    Q_j = ell^{-j} on coordinate j, Quad0 = 0, B = 1 at the top level.
    a0 = a1 = a = 1, a2 = 4/5, so the level-2 weight a*ell^2 = 4 becomes 16/5.
    """
    ell, k, a = 2, 2, 1.0
    eta = ell ** (-k)
    Q = np.diag([ell ** (-j) for j in range(k + 1)]).astype(float)
    # a_0 = a_1 = a, a_2 = a*a_1 / (a*ell^{-2} + a_1) = 1/1.25 = 0.8
    a_j = [1.0, 1.0, 0.8]
    w_const = [a * ell**j for j in range(k + 1)]
    w_aj = [a_j[j] * ell**j for j in range(k + 1)]

    def first(weights):
        # Mass is diagonal: weight_j * Q_j^2 = weight_j * ell^{-2j}
        diag = np.array([weights[j] * ell ** (-2 * j) for j in range(k + 1)])
        Quad = np.diag(diag)
        f = np.array([0.0, 0.0, 1.0])
        return eta * schur(Quad, Q, f)

    c, r = first(w_const), first(w_aj)
    return {
        "ell": ell,
        "k": k,
        "a_j": a_j,
        "weight_const_a": w_const,
        "weight_a_j": w_aj,
        "flat_first_const_a": c,
        "flat_first_a_j": r,
        "relative_diff": abs(c - r) / abs(c),
        "note": "(3.24) is the site recursion. (3.16) and (3.128) use constant a. Not one of the three readings.",
    }


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(2)
    # Six coordinates, not a geometric torus. Side cap is irrelevant:
    # the matrices are 6 by 6. Labelled stand-ins, see the module docstring.
    nE, nB, ell, k, a = 6, 2, 2, 1, 1.0
    Quad0 = np.eye(nE)
    Qlin, raw = [], []
    for _j in range(k + 1):
        Qlin.append(rng.normal(size=(nB, nE)))
        T = rng.normal(size=(nB, nE, nE))
        raw.append(0.5 * (T + np.transpose(T, (0, 2, 1))))
    J = rng.normal(size=(nE,))
    Blist = [rng.normal(size=(nB,)) for _ in range(8)]
    case = run_case(ell, k, a, Qlin, raw, Quad0, J, [0.0, 0.02, 0.08], Blist, "float-seed2-k1")
    aj = aj_shift_example()
    both = exact_model(False)
    top = exact_model(True)
    payload = {
        "float_k1": _shrink(case),
        "a_j_check": aj,
        "exact_both_levels": both,
        "exact_top_level_only": top,
    }
    path = OUT / "results.json"
    path.write_text(json.dumps(payload, indent=2))
    print(path)
    _print_summary(payload)


def _shrink(case: dict) -> dict:
    rows = []
    for rec in case["rows"]:
        readings = {}
        for kind, info in rec.get("readings", {}).items():
            readings[kind] = {kk: vv for kk, vv in info.items() if kk != "values"}
        rows.append({kk: vv for kk, vv in rec.items() if kk != "readings"} | {"readings": readings})
    return {kk: vv for kk, vv in case.items() if kk != "rows"} | {"rows": rows}


def _print_summary(payload: dict) -> None:
    case = payload["float_k1"]
    print(f"== {case['label']} eta={case['eta']} H-err={case['H_invariance_err']:.3e} ==")
    for rec in case["rows"]:
        print(f"  theta={rec['theta']} min_eig={rec['min_eig_lane']:.4g}")
        for kind, info in rec["readings"].items():
            if "ratio_spread" in info:
                print(
                    f"    {kind:12} spread={info['ratio_spread']:.8f} "
                    f"min={info['ratio_min']:.6f} max={info['ratio_max']:.6f}"
                )
            else:
                print(f"    {kind:12} {info}")
    aj = payload["a_j_check"]
    print(
        f"a_j weights const {aj['weight_const_a']} vs a_j {aj['weight_a_j']} "
        f"flat first {aj['flat_first_const_a']} vs {aj['flat_first_a_j']}"
    )
    for key in ("exact_both_levels", "exact_top_level_only"):
        block = payload[key]
        print(f"== {key} lane_pd={block['lane_pd']} theta={block['theta']} ==")
        for kind, info in block["kinds"].items():
            ratios = [row["ratio"] for row in info["rows"]]
            print(f"  {kind:12} pd={info['pd']} all_equal={info['all_equal']} spread={info['spread']}")
            print(f"    ratios {ratios}")


if __name__ == "__main__":
    main()
