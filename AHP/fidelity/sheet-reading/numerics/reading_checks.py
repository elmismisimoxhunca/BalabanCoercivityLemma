#!/usr/bin/env python3
"""Reading checks for statement-sheet Q8, Q10, Q11.

Evidence only. Nothing here is a theorem. Every modelled operator cites the
Lean definition it transcribes. The covariant SU(2) jets (QlinStepL, gradL2,
lapFull) are not transcribed: the script checks the linear-algebra shape of
the definitions that the reading questions actually turn on.

Tolerances are absolute float64 residuals. Exact a_j identities use Fraction.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent / "results.json"
TOL = 1e-9
SEED = 20261021


def fail(msg: str) -> None:
    raise SystemExit("FAIL: " + msg)


def max_abs(a) -> float:
    return float(np.max(np.abs(a))) if np.size(a) else 0.0


# ---------------------------------------------------------------------------
# Q8. a_j and the (3.24) weight.
# Lean: ajSeq, ZR2Ops2.lean:21; aSeqAux / aSeq, ConstantA.lean:155 and :160.
# Print: CMP99b p.394 (3.24), render CMP99b_p394-06.png, corpus CMP99b_p394.md.
# ---------------------------------------------------------------------------

def a_seq_aux(a: Fraction, d: Fraction, n: int) -> Fraction:
    """ConstantA.aSeqAux (ConstantA.lean:155): aSeqAux a d 0 = a,
    aSeqAux a d (n+1) = a * prev / (d + prev)."""
    x = a
    for _ in range(n):
        x = a * x / (d + x)
    return x


def a_seq(a: Fraction, ell: int, n: int) -> Fraction:
    """ConstantA.aSeq (ConstantA.lean:160): d = a / L^2."""
    return a_seq_aux(a, a / (ell * ell), n)


def aj_seq(a: Fraction, ell: int, j: int) -> Fraction:
    """ZR2Ops2.ajSeq (ZR2Ops2.lean:21): j = 0 -> a, else aSeq a ell (j-1)."""
    if j == 0:
        return a
    return a_seq(a, ell, j - 1)


def a_print(a: Fraction, ell: int, j: int) -> Fraction:
    """Printed recurrence, p.394: a_0 = a_1 = a,
    a_{j+1} = a * a_j / (a * L^{-2} + a_j)."""
    if j <= 1:
        return a
    prev = a_print(a, ell, j - 1)
    return a * prev / (a / (ell * ell) + prev)


def check_aj_and_weights() -> dict:
    rows = []
    for a, ell in ((Fraction(1), 2), (Fraction(1, 2), 3), (Fraction(3), 5)):
        for j in range(0, 7):
            got = aj_seq(a, ell, j)
            exp = a_print(a, ell, j)
            if got != exp:
                fail(f"ajSeq != print a_j at a={a}, L={ell}, j={j}: {got} vs {exp}")
            rows.append({"a": str(a), "L": ell, "j": j, "aj": str(got)})
    # The file's own examples: aSeq 1 2 0 = 1, aSeq 1 2 1 = 4/5 (ConstantA.lean:244-246).
    if a_seq(Fraction(1), 2, 0) != 1 or a_seq(Fraction(1), 2, 1) != Fraction(4, 5):
        fail("aSeq examples")
    if aj_seq(Fraction(1), 2, 2) != Fraction(4, 5):
        fail("ajSeq 2 should be a_2 = 4/5")

    # Weight. Print (3.24): (L^j eta)^{d-2}. Lean Qpa multiplies by ell^j
    # (ZR2Ops2.lean:29), docstring: d = 3, eta-free body.
    # (L^j eta)^{d-2} = eta^{d-2} * L^{j(d-2)}. At d = 3 this is eta * L^j.
    # Removing the global factor eta^{d-2} leaves L^j, which is the Lean weight.
    weight_rows = []
    for ell, k, j in ((2, 3, 0), (2, 3, 1), (2, 3, 4), (3, 2, 2)):
        eta = Fraction(1) / (ell ** k)
        d = 3
        printed = (Fraction(ell) ** j * eta) ** (d - 2)
        lean = Fraction(ell) ** j
        ratio = printed / lean
        global_factor = eta ** (d - 2)
        if ratio != global_factor:
            fail("weight ratio is not the global eta factor")
        weight_rows.append({
            "L": ell, "k": k, "j": j,
            "printed_(L^j eta)^{d-2}": str(printed),
            "lean_ell^j": str(lean),
            "ratio": str(ratio),
            "equal_after_removing_eta^{d-2}": printed / global_factor == lean,
        })
    # At eta = 1 the printed weight equals the Lean weight exactly.
    if (Fraction(2) ** 4 * 1) ** 1 != Fraction(2) ** 4:
        fail("eta=1 weight")
    # Literal unweighted reading of a later a||QA||^2 is a different number
    # once two levels are occupied. Recorded here because (3.24)'s weight and
    # (3.16)'s weight are the same shape. a = 1, |q_0| = |q_1| = 1, L = 2:
    # weighted sum a*L^0*|q0|^2 + a*L^1*|q1|^2 = 1 + 2 = 3
    # unweighted a*(|q0|^2+|q1|^2) = 2.
    weighted = 1 * (2 ** 0) + 1 * (2 ** 1)
    unweighted = 1 * (1 + 1)
    if weighted == unweighted:
        fail("weights should differ across levels")
    return {
        "aj_match_count": len(rows),
        "aj_sample": [r for r in rows if r["a"] == "1" and r["L"] == 2],
        "weights": weight_rows,
        "two_level_weighted": weighted,
        "two_level_unweighted": unweighted,
    }


# ---------------------------------------------------------------------------
# Q8. DelpA / Gp pattern, and the shape of W and Delta_pi.
# Lean: DelpA ZR2Ops2.lean:57-59, Gp ZR2Ops2.lean:63-65,
#       Wop ZR2Ops2.lean:67-69, DpiFull ZR2Ops2.lean:83-84,
#       inner_DpiFull ZR2Ops2.lean:93-97.
# This is the mask arithmetic of those lines, on a random symmetric matrix.
# It is not lapFull, gradL2, or the SU(2) curvature term.
# ---------------------------------------------------------------------------

def star_proj(n: int, rank: int, rng: np.random.Generator) -> np.ndarray:
    a = rng.normal(size=(n, rank))
    q, _ = np.linalg.qr(a)
    q = q[:, :rank]
    return q @ q.T


def check_gp_w(rng: np.random.Generator) -> dict:
    n = 6
    omega = np.array([True, True, True, True, False, False])
    mask = np.diag(omega.astype(float))
    raw = rng.normal(size=(n, n))
    m = raw.T @ raw + np.eye(n)  # stand-in for lapFull + Qpa, SPD
    # DelpA = mask (lapFull + Qpa) mask. ZR2Ops2.lean:57-59.
    delpa = mask @ m @ mask
    # Gp = inverse(DelpA + (1 - mask)) composed with mask. ZR2Ops2.lean:63-65.
    padded = delpa + (np.eye(n) - mask)
    gp = np.linalg.inv(padded) @ mask
    block = m[np.ix_(omega, omega)]
    block_inv = np.linalg.inv(block)

    support = []
    reproduce = []
    block_err = []
    for _ in range(8):
        f = rng.normal(size=n)
        gf = gp @ f
        support.append(max_abs(gf[~omega]))
        reproduce.append(max_abs(delpa @ gf - mask @ f))
        expect = np.zeros(n)
        expect[omega] = block_inv @ f[omega]
        block_err.append(max_abs(gf - expect))
    if max(support) > TOL or max(reproduce) > TOL or max(block_err) > TOL:
        fail(f"Gp_spec pattern {max(support)} {max(reproduce)} {max(block_err)}")

    # Singular Dirichlet block: Lean Ring.inverse returns 0 (Gp docstring,
    # ZR2Ops2.lean:60-65). We do not imitate that junk value; we only record
    # that the padded operator is singular, so Gp_spec's IsUnit hypothesis fails.
    m_sing = m.copy()
    idx = np.where(omega)[0]
    # Rank-one collapse of the Omega0 block: replace it by a projection of rank |Ω|-1.
    v = np.ones(len(idx))
    v /= np.linalg.norm(v)
    eye_b = np.eye(len(idx)) - np.outer(v, v)
    m_sing[np.ix_(idx, idx)] = eye_b @ m[np.ix_(idx, idx)] @ eye_b
    delpa_s = mask @ m_sing @ mask
    padded_s = delpa_s + (np.eye(n) - mask)
    svals = np.linalg.svd(padded_s, compute_uv=False)
    if svals[-1] > 1e-8:
        fail(f"expected a singular padding, smallest singular value {svals[-1]}")

    # W = I - D Gp R D*, Dpi = W* Delta W.
    # Shapes: sites n, bonds n_b. D stands for gradL2 (R2Ops1.lean:75), not transcribed.
    n_b = 9
    d_op = rng.normal(size=(n_b, n))
    r_op = star_proj(n, 2, rng)
    # Rproj is an orthogonal projection (R2Ops1.lean:170, Rproj_idem / Rproj_adjoint).
    if max_abs(r_op @ r_op - r_op) > TOL or max_abs(r_op - r_op.T) > TOL:
        fail("projection stand-in")
    w = np.eye(n_b) - d_op @ gp @ r_op @ d_op.T
    delta = rng.normal(size=(n_b, n_b))
    delta = delta.T @ delta  # stand-in for Delta, symmetric
    dpi = w.T @ delta @ w
    form_err = []
    w_err = []
    for _ in range(8):
        a = rng.normal(size=n_b)
        wa = a - d_op @ gp @ r_op @ d_op.T @ a
        w_err.append(max_abs(w @ a - wa))
        lhs = float(a @ dpi @ a)
        rhs = float(wa @ delta @ wa)
        form_err.append(abs(lhs - rhs))
    if max(w_err) > TOL or max(form_err) > TOL:
        fail(f"W / (3.119) shape {max(w_err)} {max(form_err)}")
    return {
        "gp_support_max": max(support),
        "gp_delpa_reproduce_max": max(reproduce),
        "gp_block_inverse_max": max(block_err),
        "singular_padding_smallest_sv": float(svals[-1]),
        "w_formula_max": max(w_err),
        "dpi_quadratic_max": max(form_err),
        "n_sites": n,
        "n_omega": int(omega.sum()),
        "n_bonds": n_b,
    }


# ---------------------------------------------------------------------------
# Q10. The chain G^{-1} -> G -> G_1^{-1} -> G_1 -> H_1.
# Lean: BaseDataS.Ginv / G / H, R2Algebra.lean:145-151;
#       K and IsG1inv, R2Algebra.lean:154-164;
#       K_eq, R2Algebra.lean:168-170;
#       G1 / H1, R2Algebra.lean:307-310;
#       MassFull weight, ZXR2Ops3.lean:90-91 and inner_MassFull :104-108;
#       wired G1in, ZXR2Wire2.lean:82-84; H1in, ZXR2Wire2.lean:86-88;
#       firstTerm eta, ZXG3A.lean:50-51.
# Matrix model of that algebra. Not the lattice assembly in baseData.
# ---------------------------------------------------------------------------

def check_chain(rng: np.random.Generator) -> dict:
    n_e, n_s, n_f = 6, 3, 3
    raw = rng.normal(size=(n_e, n_e))
    dpi = raw.T @ raw + 0.5 * np.eye(n_e)
    t_op = rng.normal(size=(n_s, n_e))
    q = rng.normal(size=(n_f, n_e))
    # Level weights of (3.16) at eta = 1, d = 3: a * L^j. Three constraint
    # components, standing for one level-0 row and two level-1 rows, L = 2, a = 1.
    weights = np.array([1.0, 2.0, 2.0])
    mass = q.T @ np.diag(weights) @ q
    mass_unweighted = q.T @ q  # literal a||QA||^2 with a = 1, no level weight
    ginv = dpi + t_op.T @ t_op + mass
    g = np.linalg.inv(ginv)
    qgqs = q @ g @ q.T
    h = g @ q.T @ np.linalg.inv(qgqs)

    # Quadratic C2(A) = (v·A)^2 u. Then <A, Delta2 A> = 2 <H C2(A), J>
    # gives Delta2 = 2 <H u, J> v v^T.
    v = rng.normal(size=n_e)
    v /= np.linalg.norm(v)
    u = rng.normal(size=n_f)
    jvec = rng.normal(size=n_e)
    # Scale the quadratic correction down so ||Delta2|| stays below the
    # coercivity of Ginv (the smallness (3.137) in the form used by
    # QG1Qs_isUnit_of_small, R2Algebra.lean:325-332).
    scale = 1e-3
    u = scale * u
    coeff = 2.0 * float(jvec @ h @ u)
    delta2 = coeff * np.outer(v, v)

    def c2(a: np.ndarray) -> np.ndarray:
        return float(v @ a) ** 2 * u

    def k_form(a: np.ndarray) -> float:
        # R2Algebra.K, R2Algebra.lean:154-156.
        return float(
            a @ dpi @ a
            - 2.0 * float(jvec @ h @ c2(a))
            + np.linalg.norm(t_op @ a) ** 2
            + a @ mass @ a
        )

    g1inv = ginv - delta2  # isG1inv_sub, R2Algebra.lean:236-242
    sym_err = max_abs(g1inv - g1inv.T)
    k_err = []
    keq_err = []
    weight_gap = []
    for _ in range(8):
        a = rng.normal(size=n_e)
        k_err.append(abs(float(a @ g1inv @ a) - k_form(a)))
        # K_eq: K A = <A, Ginv A> - 2 <H C2(A), J>
        keq = float(a @ ginv @ a) - 2.0 * float(jvec @ h @ c2(a))
        keq_err.append(abs(keq - k_form(a)))
        qa = q @ a
        weighted = float(qa @ np.diag(weights) @ qa)
        literal = float(qa @ qa)
        weight_gap.append(abs(weighted - literal))
    if sym_err > TOL or max(k_err) > TOL or max(keq_err) > TOL:
        fail(f"G1inv form {sym_err} {max(k_err)} {max(keq_err)}")
    if min(weight_gap) < 1e-6:
        fail("weighted and unweighted mass agreed on a random vector; rescale")

    evals = np.linalg.eigvalsh(ginv)
    evals2 = np.linalg.eigvalsh(delta2)
    # Coercivity margin: smallest eigenvalue of Ginv minus ||Delta2||.
    margin = float(evals[0] - np.linalg.norm(delta2, 2))
    if margin <= 0:
        fail(f"smallness margin {margin}")
    g1 = np.linalg.inv(g1inv)  # Ring.inverse, the unit case. R2Algebra.lean:307.
    qg1 = q @ g1 @ q.T
    sv = np.linalg.svd(qg1, compute_uv=False)
    if sv[-1] < 1e-8:
        fail("QG1Q* singular despite the smallness margin")
    h1 = g1 @ q.T @ np.linalg.inv(qg1)  # (3.129), R2Algebra.lean:308-310.
    # The formula is the definition; check it against an independent solve:
    # H1 B is the minimizer A = G1 Q* omega with Q G1 Q* omega = B.
    solve_err = []
    for _ in range(6):
        b = rng.normal(size=n_f)
        omega = np.linalg.solve(qg1, b)
        amin = g1 @ q.T @ omega
        solve_err.append(max_abs(h1 @ b - amin))
        if max_abs(q @ amin - b) > TOL:
            fail("constraint QA = B not met by the minimizer")
    if max(solve_err) > TOL:
        fail("H1")

    # Wired normalisation. G1in = eta^{-1} * (inclusion of data.G1).
    # ZXR2Wire2.lean:82-84. firstTerm multiplies by eta the inverse of
    # Nmat = Q data.G1 Q*, ZXG3A.lean:35-51. Algebra:
    # (Q (eta^{-1} G1) Q*)^{-1} = eta (Q G1 Q*)^{-1},
    # so firstTerm equals <B, (Q G1in Q*)^{-1} B>, and equals eta times
    # the unscaled inverse. The inclusion is the identity in this model.
    eta = 0.125  # L^{-k} = 2^{-3}
    g1_wired = (1.0 / eta) * g1
    q_wired = q @ g1_wired @ q.T
    wire_err = []
    factor_err = []
    for _ in range(6):
        b = rng.normal(size=n_f)
        unscaled = float(b @ np.linalg.solve(qg1, b))
        wired = float(b @ np.linalg.solve(q_wired, b))
        first = eta * unscaled
        wire_err.append(abs(first - wired))
        factor_err.append(abs(wired / unscaled - eta))
    if max(wire_err) > TOL or max(factor_err) > TOL:
        fail("eta normalisation")

    # Literal unweighted mass does not reproduce K.
    ginv_lit = dpi + t_op.T @ t_op + mass_unweighted
    lit_gap = []
    for _ in range(6):
        a = rng.normal(size=n_e)
        lit_gap.append(abs(float(a @ ginv @ a) - float(a @ ginv_lit @ a)))
    if min(lit_gap) < 1e-8:
        fail("unweighted Ginv agreed with weighted Ginv")
    return {
        "g1inv_symmetry_max": sym_err,
        "k_form_max": max(k_err),
        "k_eq_max": max(keq_err),
        "weight_gap_min": min(weight_gap),
        "ginv_smallest_eigenvalue": float(evals[0]),
        "delta2_op_norm": float(np.linalg.norm(delta2, 2)),
        "smallness_margin": margin,
        "qg1q_smallest_sv": float(sv[-1]),
        "h1_minimizer_max": max(solve_err),
        "eta": eta,
        "eta_first_term_equals_wired_inverse_max": max(wire_err),
        "wired_over_unscaled_minus_eta_max": max(factor_err),
        "unweighted_ginv_gap_min": min(lit_gap),
        "delta2_largest_abs_eigenvalue": float(np.max(np.abs(evals2))),
    }


# ---------------------------------------------------------------------------
# Q11. B-tilde and C = id - h Q on a side-4 torus, ell = 2.
# Lean transcribed:
#   periodicLatticeShift, ClayStatement.lean:1281-1283 (sites: L mu + 1)
#   droppedBondLast, ReparamCDisjoint.lean:157-158
#   pathSite, QOne.lean:175-176
#   blockOf / inBlock, AdmissibleSubspace.lean:120-124 and :111-114
#   CoarseLattice, AdmissibleSubspace.lean:154 (membership :157)
#   staircasePath / corner1 / corner2 / axisSegment,
#       AdmissibleSubspace.lean:328-331, :331-333, :294-297, :366-370
#   Ax, AxialContour.lean:153-154
#   LamPrime, CRowIn, IsDroppedIn, OnLambda, OnLambdaTildeIn,
#       ZStatementP428.lean:205-234
#   OnLambdaT, ZR2A.lean:121-123
#   iotaD, rhoD, H0, H0inv, hLift, Cop, Cop_id, Cop_ker,
#       ZXR2Unit2.lean:40-107 and :127-146
# One real component. SuTwo is an R^3-vector space and Cop is R-linear,
# so one component tests the same matrix. Q is NOT Q1jet (ZXR2Unit1.lean:70);
# Q1jet calls the Frechet jet QlinStepL (ZLocJet.lean:39), which is not modelled.
# ---------------------------------------------------------------------------

SIDE = 4  # number of sites = L_mu + 1. ell = 2 divides SIDE.
ELL = 2


def sites():
    return [(x, y, z) for x in range(SIDE) for y in range(SIDE) for z in range(SIDE)]


def shift(p, mu):
    q = list(p)
    q[mu] = (q[mu] + 1) % SIDE
    return tuple(q)


def path_site(p, mu, i):
    for _ in range(i):
        p = shift(p, mu)
    return p


def coarse_shift(p, mu):
    return path_site(p, mu, ELL)


def bonds():
    return [(p, mu) for p in sites() for mu in range(3)]


def coarse_sites():
    return [p for p in sites() if all(c % ELL == 0 for c in p)]


def coarse_bonds():
    return [(p, mu) for p in coarse_sites() for mu in range(3)]


def in_block(y, x):
    return all(y[mu] <= x[mu] < y[mu] + ELL for mu in range(3))


def block_of(y):
    return [x for x in sites() if in_block(y, x)]


def axis_segment(base, mu, a, b):
    """AdmissibleSubspace.axisSegment, AdmissibleSubspace.lean:294-297.
    Integer .val comparison, no extra wrap."""
    out = []
    for p, nu in bonds():
        if nu != mu:
            continue
        if any(p[k] != base[k] for k in range(3) if k != mu):
            continue
        if a <= p[mu] < b:
            out.append((p, nu))
    return out


def corner1(y, x):
    q = list(y)
    q[2] = x[2]
    return tuple(q)


def corner2(y, x):
    q = list(corner1(y, x))
    q[1] = x[1]
    return tuple(q)


def staircase(y, x):
    return (
        axis_segment(y, 2, min(y[2], x[2]), max(y[2], x[2]))
        + axis_segment(corner1(y, x), 1, min(y[1], x[1]), max(y[1], x[1]))
        + axis_segment(corner2(y, x), 0, min(y[0], x[0]), max(y[0], x[0]))
    )


def ax(y):
    acc = []
    for x in block_of(y):
        if x != y:
            acc.extend(staircase(y, x))
    return acc


def dropped(c):
    base, mu = c
    return (path_site(base, mu, ELL - 1), mu)


def lam_prime(lam_set):
    return [y for y in coarse_sites() if all(x in lam_set for x in block_of(y))]


def c_row_in(c, prime):
    base, mu = c
    return base in prime or coarse_shift(base, mu) in prime


def index(items):
    return {item: i for i, item in enumerate(items)}


def check_staircase_transcription():
    """A hand instance of staircasePath, AdmissibleSubspace.lean:366-370."""
    y = (0, 0, 0)
    x = (1, 1, 0)
    got = set(staircase(y, x))
    expect = {((0, 0, 0), 1), ((0, 1, 0), 0)}
    if got != expect:
        fail(f"staircase transcription {got}")
    # x = (1,0,0): only the last leg, one bond.
    if set(staircase(y, (1, 0, 0))) != {((0, 0, 0), 0)}:
        fail("staircase single leg")
    if len(block_of(y)) != ELL ** 3:
        fail("block size")


def build_geometry(lam_sites):
    lam = set(lam_sites)
    prime = lam_prime(lam)
    prime_set = set(prime)
    cb = coarse_bonds()
    bb = bonds()
    rows = [c for c in cb if c_row_in(c, prime_set)]
    ax_bonds = set()
    for y in prime:
        ax_bonds.update(ax(y))
    dropped_bonds = {dropped(c) for c in rows}
    return {
        "lam": lam,
        "prime": prime,
        "bonds": bb,
        "coarse": cb,
        "rows": rows,
        "ax": ax_bonds,
        "dropped": dropped_bonds,
        "b_index": index(bb),
        "c_index": index(cb),
    }


def free_bond(geom):
    """A bond a touching tilde field may use: touches Lambda, not axial, not dropped."""
    lam = geom["lam"]
    for b in geom["bonds"]:
        p, mu = b
        touches = p in lam or shift(p, mu) in lam
        if touches and b not in geom["ax"] and b not in geom["dropped"]:
            return b
    fail("no bond available to a touching tilde field")


def q_matrix(geom, kind: str) -> np.ndarray:
    """Linear Q: coarse bonds -> from bond fields. Not Q1jet."""
    bb = geom["bonds"]
    cb = geom["coarse"]
    bi = geom["b_index"]
    q = np.zeros((len(cb), len(bb)))
    rows = geom["rows"]
    row_pos = {c: i for i, c in enumerate(rows)}
    free = free_bond(geom)
    for c in cb:
        base, mu = c
        ci = geom["c_index"][c]
        if kind == "path":
            # Decoupled path sum. Last weight is nonzero, so H0 is invertible,
            # and the path of c does not contain another row's dropped bond
            # (checked below).
            for i, w in enumerate((1.0, 2.0)):
                b = (path_site(base, mu, i), mu)
                q[ci, bi[b]] += w
        elif kind == "free":
            # Reads one tilde-legal bond plus its own dropped bond.
            # H0 = 2 I, because `free` is not a dropped bond.
            q[ci, bi[dropped(c)]] += 2.0
            if c in row_pos:
                q[ci, bi[free]] += 1.0
        elif kind == "coupled_dropped":
            q[ci, bi[dropped(c)]] += 2.0
            # Couple to the next constraint row's dropped bond.
            if c in row_pos:
                nxt = rows[(row_pos[c] + 1) % len(rows)]
                q[ci, bi[dropped(nxt)]] += 0.3
        elif kind == "ignores_dropped":
            # Reads only the first bond of the path. H0 is the zero matrix.
            b = (path_site(base, mu, 0), mu)
            q[ci, bi[b]] += 1.0
        else:
            fail(kind)
    return q


def cop_from_q(geom, q: np.ndarray):
    """iotaD, rhoD, H0, H0inv, hLift, Cop. ZXR2Unit2.lean:40-107.
    H0inv is the inverse when H0 is bijective, else 0 (line 90-96)."""
    bb = geom["bonds"]
    cb = geom["coarse"]
    rows = geom["rows"]
    bi = geom["b_index"]
    n_b = len(bb)
    n_d = len(rows)
    iota = np.zeros((n_b, n_d))
    for j, c in enumerate(rows):
        iota[bi[dropped(c)], j] = 1.0
    # rho reads the coarse components in `rows` out of a full coarse vector.
    rho = np.zeros((n_d, len(cb)))
    for j, c in enumerate(rows):
        rho[j, geom["c_index"][c]] = 1.0
    h0 = rho @ q @ iota
    svals = np.linalg.svd(h0, compute_uv=False) if n_d else np.array([1.0])
    bijective = n_d > 0 and float(svals[-1]) > 1e-8
    if bijective:
        h0inv = np.linalg.inv(h0)
    else:
        h0inv = np.zeros((n_d, n_d))
    h = iota @ h0inv @ rho
    cop = np.eye(n_b) - h @ q
    return cop, h0, bijective, float(svals[-1]) if n_d else 0.0


def on_lambda_t(geom, bvec) -> bool:
    bi = geom["b_index"]
    lam = geom["lam"]
    for b, val in zip(geom["bonds"], bvec):
        p, mu = b
        touches = p in lam or shift(p, mu) in lam
        if not touches and abs(val) > TOL:
            return False
    return True


def on_lambda_both(geom, bvec) -> bool:
    bi = geom["b_index"]
    lam = geom["lam"]
    for b, val in zip(geom["bonds"], bvec):
        p, mu = b
        both = p in lam and shift(p, mu) in lam
        if not both and abs(val) > TOL:
            return False
    return True


def on_tilde(geom, bvec) -> bool:
    bi = geom["b_index"]
    for b in geom["ax"]:
        if abs(bvec[bi[b]]) > TOL:
            return False
    for b in geom["dropped"]:
        if abs(bvec[bi[b]]) > TOL:
            return False
    return True


def random_tilde(geom, rng, touching: bool) -> np.ndarray:
    v = np.zeros(len(geom["bonds"]))
    lam = geom["lam"]
    forbidden = set(geom["ax"]) | set(geom["dropped"])
    for i, b in enumerate(geom["bonds"]):
        p, mu = b
        if b in forbidden:
            continue
        touches = p in lam or shift(p, mu) in lam
        both = p in lam and shift(p, mu) in lam
        if touching and touches:
            v[i] = rng.normal()
        if not touching and both:
            v[i] = rng.normal()
    return v


def check_cop(rng: np.random.Generator) -> dict:
    check_staircase_transcription()
    # One block of the origin. Proper nonempty Lambda, not the whole torus.
    lam_sites = [p for p in sites() if all(c < ELL for c in p)]
    geom = build_geometry(lam_sites)
    if geom["prime"] != [(0, 0, 0)]:
        fail(f"LamPrime {geom['prime']}")
    if len(geom["rows"]) == 0:
        fail("no constraint rows")
    # Dropped bonds of distinct rows are distinct (iota is injective).
    if len(geom["dropped"]) != len(geom["rows"]):
        fail("dropped bonds collide")

    # Path of a row does not contain another row's dropped bond.
    for c in geom["rows"]:
        base, mu = c
        path_bonds = {(path_site(base, mu, i), mu) for i in range(ELL)}
        foreign = geom["dropped"] - {dropped(c)}
        if path_bonds & foreign:
            fail(f"path reads a foreign dropped bond: {c}")

    touch_only = []
    both = []
    for b in geom["bonds"]:
        p, mu = b
        t = p in geom["lam"] or shift(p, mu) in geom["lam"]
        bo = p in geom["lam"] and shift(p, mu) in geom["lam"]
        if t and not bo:
            touch_only.append(b)
        if bo:
            both.append(b)
    if not touch_only or not both:
        fail("expected both bond classes to be nonempty")

    out = {
        "side": SIDE,
        "ell": ELL,
        "n_bonds": len(geom["bonds"]),
        "n_coarse_bonds": len(geom["coarse"]),
        "n_lam_prime": len(geom["prime"]),
        "n_constraint_rows": len(geom["rows"]),
        "n_ax_bonds": len(geom["ax"]),
        "n_both_endpoint_bonds": len(both),
        "n_touching_only_bonds": len(touch_only),
        "dropped_outside_both": sorted(
            [list(b[0]) + [b[1]] for b in geom["dropped"] if b not in both]
        ),
    }

    samples = 6
    free = free_bond(geom)
    out["free_bond"] = [list(free[0]), free[1]]
    # Path bonds of every constraint row, classified against the tilde support.
    path_class = []
    for c in geom["rows"]:
        base, mu = c
        for i in range(ELL):
            b = (path_site(base, mu, i), mu)
            p, nu = b
            touches = p in geom["lam"] or shift(p, nu) in geom["lam"]
            path_class.append({
                "on_ax": b in geom["ax"],
                "dropped": b in geom["dropped"],
                "touches_lambda": touches,
            })
    out["path_bonds_visible_to_tilde"] = sum(
        1 for r in path_class if r["touches_lambda"] and not r["on_ax"] and not r["dropped"]
    )
    for kind in ("path", "free", "coupled_dropped", "ignores_dropped"):
        q = q_matrix(geom, kind)
        cop, h0, bij, sv = cop_from_q(geom, q)
        id_err = []
        ker_err = []
        nonzero_b0 = []
        scalar_err = []
        naive_ker = []
        tilde_ok = 0
        tilde_ker = []
        tilde_id = []
        both_ok = 0
        for _ in range(samples):
            b = rng.normal(size=len(geom["bonds"]))
            cb = cop @ b
            # Cop_id: identity off the dropped bonds. ZXR2Unit2.lean:127-134.
            for i, bond in enumerate(geom["bonds"]):
                if bond not in geom["dropped"]:
                    id_err.append(abs(cb[i] - b[i]))
            # Cop_ker, only claimed when H0 is bijective. ZXR2Unit2.lean:136-146.
            qcb = q @ cb
            for c in geom["rows"]:
                ker_err.append(abs(qcb[geom["c_index"][c]]))
            if kind == "path" and bij:
                # Scalar solution of (Q B)(c) = 0 for the single variable B(b0),
                # other path bonds held at their original values (C is the
                # identity there). Weight (1, 2) on i = 0, 1.
                for c in geom["rows"]:
                    base, mu = c
                    b0 = dropped(c)
                    b_first = (path_site(base, mu, 0), mu)
                    expect = -0.5 * b[geom["b_index"][b_first]]
                    scalar_err.append(abs(cb[geom["b_index"][b0]] - expect))
                    nonzero_b0.append(abs(expect))
            if kind == "coupled_dropped" and bij:
                # Naive one-bond formula that freezes the neighbouring b0
                # does not solve the joint system. Cop does.
                rows = geom["rows"]
                naive = b.copy()
                for i, c in enumerate(rows):
                    nxt = rows[(i + 1) % len(rows)]
                    # 2 x_i + 0.3 B(b0 of next) = 0, freezing the neighbour.
                    naive[geom["b_index"][dropped(c)]] = -0.15 * b[geom["b_index"][dropped(nxt)]]
                naive_ker.append(max_abs((q @ naive)[[geom["c_index"][c] for c in rows]]))
                # The joint solution of a dropped-only system is zero on b0.
                for c in rows:
                    nonzero_b0.append(abs(cb[geom["b_index"][dropped(c)]]))
        bt = random_tilde(geom, rng, touching=True)
        if not (on_tilde(geom, bt) and on_lambda_t(geom, bt)):
            fail("random touching tilde field missed its predicate")
        if on_lambda_both(geom, bt):
            fail("touching tilde field unexpectedly had both-endpoint support")
        tilde_ok = 1
        cbt = cop @ bt
        if bij:
            for c in geom["rows"]:
                tilde_ker.append(abs((q @ cbt)[geom["c_index"][c]]))
        for i, bond in enumerate(geom["bonds"]):
            if bond not in geom["dropped"]:
                tilde_id.append(abs(cbt[i] - bt[i]))
        bb = random_tilde(geom, rng, touching=False)
        if not (on_tilde(geom, bb) and on_lambda_both(geom, bb) and on_lambda_t(geom, bb)):
            fail("both-endpoint tilde field")
        both_ok = 1
        moved = max_abs(cbt[[geom["b_index"][dropped(c)] for c in geom["rows"]]])
        rec = {
            "h0_bijective": bij,
            "h0_smallest_sv": sv,
            "cop_id_max": max(id_err) if id_err else 0.0,
            "q_cop_max_on_rows": max(ker_err) if ker_err else 0.0,
            "tilde_predicate_ok": tilde_ok,
            "tilde_cop_id_max": max(tilde_id) if tilde_id else 0.0,
            "tilde_q_cop_max": max(tilde_ker) if tilde_ker else None,
            "both_endpoint_predicate_ok": both_ok,
            "path_c_moves_b0_of_tilde": moved,
        }
        if kind == "path":
            rec["scalar_solution_max"] = max(scalar_err)
            rec["scalar_solution_nonvacuous_max"] = max(nonzero_b0)
            if not bij or max(id_err) > TOL or max(ker_err) > TOL or max(scalar_err) > TOL:
                fail(f"path Cop {rec}")
            if max(nonzero_b0) < 1e-3:
                fail("scalar solution was vacuously zero")
            # On this one-block Lambda every path bond is axial, dropped, or
            # outside Lambda, so a tilde field is already in the kernel and C
            # does not have to move b0. That is a fact about this Q, not about Cop.
            if out["path_bonds_visible_to_tilde"] != 0:
                fail("expected the straight path to miss the tilde support")
            if max(tilde_ker) > TOL:
                fail("tilde path kernel")
        elif kind == "free":
            # (C Bt)(b0) = -B(free)/2, nonzero when Bt(free) is nonzero.
            expect = -0.5 * bt[geom["b_index"][free]]
            move_err = max(
                abs(cbt[geom["b_index"][dropped(c)]] - expect) for c in geom["rows"]
            )
            rec["tilde_b0_equals_scalar_max"] = move_err
            rec["tilde_b0_value"] = expect
            if (
                not bij or max(id_err) > TOL or max(ker_err) > TOL
                or max(tilde_ker) > TOL or move_err > TOL or abs(expect) < 1e-8
            ):
                fail(f"free Cop {rec}")
        elif kind == "coupled_dropped":
            rec["naive_one_bond_residual_min"] = min(naive_ker)
            rec["cop_b0_max"] = max(nonzero_b0)
            if not bij or max(ker_err) > TOL or max(id_err) > TOL:
                fail(f"coupled Cop {rec}")
            if min(naive_ker) < 1e-6:
                fail("naive one-bond formula unexpectedly solved the coupled system")
            if max(nonzero_b0) > TOL:
                fail("coupled dropped-only system should set b0 to 0")
        else:
            # Junk branch: H0 is singular, H0inv = 0, C = id, constraint not solved.
            if bij or max(id_err) > TOL:
                fail(f"junk branch {rec}")
            # C = id, so Q(CB) = QB, which reads the first path bond and is not zero.
            if max(ker_err) < 1e-6:
                fail("singular H0 unexpectedly still solved the constraint")
        out[kind] = rec
    return out


def main():
    rng = np.random.default_rng(SEED)
    result = {
        "seed": SEED,
        "tolerance": TOL,
        "q8_weights": check_aj_and_weights(),
        "q8_gp_w": check_gp_w(rng),
        "q10_chain": check_chain(rng),
        "q11_cop": check_cop(rng),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "q8_aj_match_count": result["q8_weights"]["aj_match_count"],
        "q8_aj_L2": result["q8_weights"]["aj_sample"],
        "q8_two_level": [
            result["q8_weights"]["two_level_weighted"],
            result["q8_weights"]["two_level_unweighted"],
        ],
        "q8_gp": result["q8_gp_w"],
        "q10": result["q10_chain"],
        "q11_counts": {k: result["q11_cop"][k] for k in (
            "n_bonds", "n_constraint_rows", "n_ax_bonds",
            "n_both_endpoint_bonds", "n_touching_only_bonds")},
        "q11_path_scalar": result["q11_cop"]["path"]["scalar_solution_max"],
        "q11_path_kernel": result["q11_cop"]["path"]["q_cop_max_on_rows"],
        "q11_coupled_naive_min": result["q11_cop"]["coupled_dropped"]["naive_one_bond_residual_min"],
        "q11_junk_kernel": result["q11_cop"]["ignores_dropped"]["q_cop_max_on_rows"],
    }, indent=2))
    print("ALL READING CHECKS PASSED")
    print("wrote", OUT)


if __name__ == "__main__":
    main()
