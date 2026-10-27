#!/usr/bin/env python3
"""Independent attack check for the s3-normalisation exact witness.

Evidence only. Not a theorem.

This script deliberately does NOT import first_term_readings.py. It
re-transcribes the witness from SPEC.md and uses a different computational
path:
  * determinants by the fraction-free Bareiss algorithm (the design script
    uses Gauss-Jordan inversion and a pivot-product Sylvester test),
  * Schur values by solving the saddle-point system
        [S  Q^T] [x]   [0]
        [Q  0  ] [y] = [f],   value = -<f, y>,
    instead of forming Q S^{-1} Q^T and inverting it.

Checks (each printed, all must be True):
  1. rank Q = 4 (full row rank; needed for Nmat invertibility).
  2. J = (3/2, 2, 3/2, 1) gives H* J = (1,1,1,1) (both levels active).
  3. Exact H-invariance: lam(eta * Quad) == lam(Quad) in rationals
     (the design script only checks this in floats).
  4. All four S operators (lane, plainH, draft, linearEta) and uniformBody
     have all leading principal minors > 0 (Bareiss), so the inverses in the
     first term are genuine, not the Lean junk value 0.
  5. det(Q S^{-1} Q^T) != 0 for each S (recorded).
  6. The refuting pairs: ratio(B=(1,0)) != ratio(B=(0,1)) for plainH,
     draft, linearEta; equality with scalar 1 for uniformBody.
  7. Top-level-only variant: plainH ratio = 1, draft = 29/28,
     linearEta = 29/26 on both B.

Lean lines transcribed (same citations as first_term_readings.py):
  eta = ell^{-k}            ZXR2Wire2.lean:37
  Q_j = ell^{-j} Qlin_j     ZXR2Sector.lean:100
  C_lane_j = ell^{-j} raw_j ZXR2Sector.lean:111
  mass weight a * ell^j     ZXR2Ops3.lean:99  (form at :112)
  H = G Q* (Q G Q*)^{-1}    R2Algebra.lean:147,149-150
  K = <A,Quad A> - 2<H(CA),J>  R2Algebra.lean:153 (Quad = Ginv, :145)
  first term eta * <tau* B, (Q S^{-1} Q*)^{-1} tau* B>  ZXG3A.lean:35,50
  tau* = B at level k, 0 below, no scalar  ZXG3A.lean:46-49, ZGU1D.lean:55,67
"""

from fractions import Fraction

# ---------- fraction-free / solve-based linear algebra ----------


def bareiss_det(M):
    """Exact determinant by the Bareiss algorithm."""
    n = len(M)
    A = [list(map(Fraction, row)) for row in M]
    sign = 1
    prev = Fraction(1)
    for k in range(n - 1):
        if A[k][k] == 0:
            swap = None
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    swap = r
                    break
            if swap is None:
                return Fraction(0)
            A[k], A[swap] = A[swap], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev
        prev = A[k][k]
        for i in range(k + 1, n):
            A[i][k] = Fraction(0)
    return sign * A[n - 1][n - 1]


def rank(M):
    A = [list(map(Fraction, row)) for row in M]
    rows, cols = len(A), len(A[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r


def solve(M, b):
    """Solve M x = b exactly by Gauss elimination with partial pivoting."""
    n = len(M)
    A = [list(map(Fraction, M[i])) + [Fraction(b[i])] for i in range(n)]
    for col in range(n):
        piv = next(i for i in range(col, n) if A[i][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [a - f * x for a, x in zip(A[r], A[col])]
    return [A[i][n] for i in range(n)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(c) for c in zip(*A)]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


# ---------- witness, re-transcribed from SPEC.md ----------

ELL, K, A_MASS = 2, 1, 1
ETA = Fraction(1, ELL) ** K           # ZXR2Wire2.lean:37
THETA = Fraction(1, 10)
QLIN = [
    [[1, 0, 1, 0], [0, 1, 0, 1]],
    [[1, 1, 0, 0], [0, 1, 1, 0]],
]
# Q_j = ell^{-j} Qlin_j, ZXR2Sector.lean:100; stacked
Q = [list(map(Fraction, row)) for row in QLIN[0]] + [
    [Fraction(x, ELL) for x in row] for row in QLIN[1]
]
RAW = [
    [[1, 0, 0, 0], [0, 1, 1, 0]],     # level-0 rank-one directions
    [[0, 0, 1, 0], [1, 0, 1, 1]],     # level-1 rank-one directions
]


def vv(v):
    return [[Fraction(v[i] * v[j]) for j in range(4)] for i in range(4)]


def quad_matrix():
    """Quad0 = I plus Mass, weights a*ell^j (ZXR2Ops3.lean:99,112)."""
    M = [[Fraction(int(i == j)) for j in range(4)] for i in range(4)]
    for j in range(2):
        Qj = Q[2 * j : 2 * j + 2]
        QtQ = matmul(transpose(Qj), Qj)
        w = Fraction(A_MASS * ELL**j)
        M = [[M[i][k] + w * QtQ[i][k] for k in range(4)] for i in range(4)]
    return M


QUAD = quad_matrix()


def lam_of(Quad):
    """H* J with H = G Q* (Q G Q*)^{-1} (R2Algebra.lean:147,149-150),
    computed by solves, not inversions. J = (3/2, 2, 3/2, 1)."""
    J = [Fraction(3, 2), Fraction(2), Fraction(3, 2), Fraction(1)]
    GJ = solve(Quad, J)                       # G J
    GQt = [solve(Quad, list(Q[c])) for c in range(4)]
    GQt = transpose(GQt)                      # G Q^T, 4x4
    N = matmul(Q, GQt)                        # Q G Q^T, 4x4
    return solve(N, [dot(Q[r], GJ) for r in range(4)])  # N^{-1} Q G J


def cross(lam, factors, zero_level0=False):
    """Symmetric S_c with <A, S_c A> = 2 <H(C A), J> (R2Algebra.lean:153).
    C(A)_b = THETA * factor * (v.A)^2; all T_j symmetric so no extra sym."""
    M = [[Fraction(0)] * 4 for _ in range(4)]
    off = 0
    for j in range(2):
        for b in range(2):
            if not (zero_level0 and j == 0):
                T = vv(RAW[j][b])
                w = 2 * lam[off] * THETA * factors[j]
                M = [[M[i][k] + w * T[i][k] for k in range(4)] for i in range(4)]
            off += 1
    return M


def s_operator(kind, zero_level0=False):
    facs = {
        "lane": [Fraction(1), Fraction(1, ELL)],          # ZXR2Sector.lean:111
        "plainH": [ETA**2, ETA**2],
        "draft": [Fraction(1), Fraction(1, ELL)],
        "linearEta": [Fraction(1), Fraction(1)],
        "uniformBody": [ETA, ETA / ELL],
    }[kind]
    Sc = cross(LAM, facs, zero_level0)
    base = QUAD if kind == "lane" else [[ETA * x for x in row] for row in QUAD]
    return [[base[i][j] - Sc[i][j] for j in range(4)] for i in range(4)]


def leading_minors_positive(M):
    return all(bareiss_det([row[:k] for row in M[:k]]) > 0 for k in range(1, len(M) + 1))


def schur_value(S, B):
    """<tau* B, (Q S^{-1} Q*)^{-1} tau* B> via the saddle-point solve."""
    f = [Fraction(0), Fraction(0), Fraction(B[0]), Fraction(B[1])]  # tau*, ZXG3A.lean:46-49
    n = 8
    M = [[Fraction(0)] * (n + 1) for _ in range(n)]
    for i in range(4):
        for j in range(4):
            M[i][j] = S[i][j]
            M[4 + i][j] = Q[i][j]
            M[i][4 + j] = Q[j][i]
    for i in range(4):
        M[4 + i][n] = f[i]
    xs = solve([row[:n] for row in M], [row[n] for row in M])
    y = xs[4:]
    return -dot(f, y)


def nmat_det(S):
    GQt = transpose([solve(S, list(Q[c])) for c in range(4)])
    return bareiss_det(matmul(Q, GQt))


LAM = lam_of(QUAD)
checks = []

checks.append(("rank Q = 4", rank(Q) == 4))
checks.append(("J gives H*J = (1,1,1,1)", LAM == [Fraction(1)] * 4))
checks.append(("exact H-invariance lam(eta*Quad) == lam(Quad)",
               lam_of([[ETA * x for x in row] for row in QUAD]) == LAM))

BS = [(1, 0), (0, 1), (1, 2), (3, -1)]

for zero0, tag in ((False, "both levels"), (True, "top level only")):
    SL = s_operator("lane", zero0)
    checks.append((f"lane S PD ({tag})", leading_minors_positive(SL)))
    checks.append((f"det Nmat lane != 0 ({tag})", nmat_det(SL) != 0))
    frozen = {B: ETA * schur_value(SL, B) for B in BS}
    if not zero0:
        checks.append(("frozen values 14/5, 12/5, 64/5, 27",
                       [frozen[B] for B in BS] == [Fraction(14, 5), Fraction(12, 5),
                                                   Fraction(64, 5), Fraction(27)]))
    ratios = {}
    for kind in ("plainH", "draft", "linearEta", "uniformBody"):
        SP = s_operator(kind, zero0)
        checks.append((f"{kind} S PD ({tag})", leading_minors_positive(SP)))
        checks.append((f"det Nmat {kind} != 0 ({tag})", nmat_det(SP) != 0))
        ratios[kind] = {B: frozen[B] / schur_value(SP, B) for B in BS}
    if not zero0:
        for kind in ("plainH", "draft", "linearEta"):
            checks.append((f"{kind} ratio split (both levels)",
                           ratios[kind][(1, 0)] != ratios[kind][(0, 1)]))
    else:
        # the design claims B-INDEPENDENT ratios here (constants 1, 29/28, 29/26)
        for kind in ("plainH", "draft", "linearEta"):
            checks.append((f"{kind} ratio B-independent (top level only)",
                           len({ratios[kind][B] for B in BS}) == 1))
    checks.append((f"uniformBody scalar 1 ({tag})",
                   all(ratios["uniformBody"][B] == 1 for B in BS)))
    if not zero0:
        checks.append(("plainH pair 56/57 vs 48/53",
                       ratios["plainH"][(1, 0)] == Fraction(56, 57)
                       and ratios["plainH"][(0, 1)] == Fraction(48, 53)))
        checks.append(("draft pair 14/13 vs 4/3",
                       ratios["draft"][(1, 0)] == Fraction(14, 13)
                       and ratios["draft"][(0, 1)] == Fraction(4, 3)))
        checks.append(("linearEta pair 7/6 vs 3/2",
                       ratios["linearEta"][(1, 0)] == Fraction(7, 6)
                       and ratios["linearEta"][(0, 1)] == Fraction(3, 2)))
    else:
        checks.append(("top-only plainH = 1",
                       all(ratios["plainH"][B] == 1 for B in BS)))
        checks.append(("top-only draft = 29/28",
                       all(ratios["draft"][B] == Fraction(29, 28) for B in BS)))
        checks.append(("top-only linearEta = 29/26",
                       all(ratios["linearEta"][B] == Fraction(29, 26) for B in BS)))

width = max(len(name) for name, _ in checks)
ok = True
for name, passed in checks:
    ok = ok and passed
    print(f"{name:{width}}  {'PASS' if passed else 'FAIL'}")
print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
