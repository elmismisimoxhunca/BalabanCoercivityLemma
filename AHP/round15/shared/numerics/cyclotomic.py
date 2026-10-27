#!/usr/bin/env python3
"""Small exact arithmetic layer for Q(zeta_N), N a power of two.

Used only to make the numerical collar dictionary explicit.  No floating-point
result is promoted to a theorem.
"""
from fractions import Fraction
import mpmath as mp


def rat_solve(A, b):
    """Solve a square Fraction system by exact Gauss-Jordan elimination."""
    n = len(b)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if M[r][col]), None)
        if pivot is None:
            raise ZeroDivisionError("singular rational system")
        M[col], M[pivot] = M[pivot], M[col]
        z = M[col][col]
        M[col] = [v / z for v in M[col]]
        for r in range(n):
            if r == col:
                continue
            z = M[r][col]
            if z:
                M[r] = [x - z * y for x, y in zip(M[r], M[col])]
    return [M[i][-1] for i in range(n)]


class Cyc:
    """An element of Q(zeta), with zeta=exp(2*pi*i/N) and N=2*degree."""
    __slots__ = ("N", "terms")

    def __init__(self, N, terms=None):
        assert N > 0 and N % 2 == 0
        self.N = N
        self.terms = {}
        if terms:
            for k, v in terms.items():
                self._add_term(k, v)

    @property
    def degree(self):
        return self.N // 2

    def _add_term(self, k, v):
        v = Fraction(v)
        if not v:
            return
        k %= self.N
        sign = 1
        if k >= self.degree:
            k -= self.degree
            sign = -1
        z = self.terms.get(k, Fraction(0)) + sign * v
        if z:
            self.terms[k] = z
        elif k in self.terms:
            del self.terms[k]

    def __add__(self, other):
        other = self.coerce(other)
        out = Cyc(self.N, self.terms)
        for k, v in other.terms.items():
            out._add_term(k, v)
        return out

    def __neg__(self):
        return Cyc(self.N, {k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __mul__(self, other):
        other = self.coerce(other)
        out = Cyc(self.N)
        for k, v in self.terms.items():
            for l, w in other.terms.items():
                out._add_term(k + l, v * w)
        return out

    def __rmul__(self, other):
        return self * other

    def coerce(self, value):
        if isinstance(value, Cyc):
            assert value.N == self.N
            return value
        return Cyc(self.N, {0: Fraction(value)})

    def inverse(self):
        if not self.terms:
            raise ZeroDivisionError("zero cyclotomic element")
        if len(self.terms) == 1:
            k, v = next(iter(self.terms.items()))
            # zeta^degree=-1, so 1/(v*zeta^k)=zeta^(N-k)/v.
            return Cyc(self.N, {(-k) % self.N: 1 / v})
        d = self.degree
        columns = []
        for j in range(d):
            col = []
            basis = Cyc(self.N, {j: 1})
            product = self * basis
            for i in range(d):
                col.append(product.terms.get(i, Fraction(0)))
            columns.append(col)
        A = [[columns[j][i] for j in range(d)] for i in range(d)]
        coeffs = rat_solve(A, [Fraction(1) if i == 0 else Fraction(0) for i in range(d)])
        return Cyc(self.N, {i: coeffs[i] for i in range(d) if coeffs[i]})

    def __truediv__(self, other):
        return self * self.coerce(other).inverse()

    def __bool__(self):
        return bool(self.terms)

    def __eq__(self, other):
        other = self.coerce(other)
        return (self - other).terms == {}

    def __hash__(self):
        return hash((self.N, tuple(sorted(self.terms.items()))))

    def numeric(self, dps=80):
        old = mp.mp.dps
        mp.mp.dps = dps
        z = mp.mpc(0)
        for k, v in self.terms.items():
            z += mp.mpf(v.numerator) / v.denominator * mp.exp(2j * mp.pi * k / self.N)
        mp.mp.dps = old
        return z

    def expression(self):
        if not self.terms:
            return "0"
        parts = []
        for k, v in sorted(self.terms.items()):
            coeff = str(v)
            if k == 0:
                parts.append(coeff)
            else:
                parts.append(f"({coeff})*zeta^{k}")
        return " + ".join(parts).replace("+ -", "- ")

    def json(self):
        return {"expression": self.expression(),
                "terms": [[k, str(v)] for k, v in sorted(self.terms.items())]}


def zero(N):
    return Cyc(N)


def one(N):
    return Cyc(N, {0: 1})


def mat_zero(N, n, m=None):
    m = n if m is None else m
    return [[Cyc(N) for _ in range(m)] for _ in range(n)]


def mat_add(A, B):
    return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mat_neg(A):
    return [[-a for a in row] for row in A]


def mat_sub(A, B):
    return mat_add(A, mat_neg(B))


def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    N = A[0][0].N
    out = mat_zero(N, n, m)
    for i in range(n):
        for j in range(m):
            for l in range(k):
                out[i][j] = out[i][j] + A[i][l] * B[l][j]
    return out


def mat_inverse(A):
    n = len(A)
    N = A[0][0].N
    M = [list(row) + [Cyc(N, {0: 1}) if i == j else Cyc(N) for j in range(n)]
         for i, row in enumerate(A)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if M[r][col]), None)
        if pivot is None:
            raise ZeroDivisionError("singular cyclotomic matrix")
        M[col], M[pivot] = M[pivot], M[col]
        z = M[col][col]
        M[col] = [v / z for v in M[col]]
        for r in range(n):
            if r == col:
                continue
            z = M[r][col]
            if z:
                M[r] = [x - z * y for x, y in zip(M[r], M[col])]
    return [row[n:] for row in M]


def mat_det(A):
    n = len(A)
    N = A[0][0].N
    M = [list(row) for row in A]
    det = Cyc(N, {0: 1})
    sign = 1
    for col in range(n):
        pivot = next((r for r in range(col, n) if M[r][col]), None)
        if pivot is None:
            return Cyc(N)
        if pivot != col:
            M[col], M[pivot] = M[pivot], M[col]
            sign *= -1
        z = M[col][col]
        det = det * z
        for r in range(col + 1, n):
            factor = M[r][col] / z
            if factor:
                M[r] = [x - factor * y for x, y in zip(M[r], M[col])]
    return det if sign == 1 else -det


def identify(z, N, dps=70, denominator=1000000):
    """Identify z in Q(zeta_N), returning exact rational basis coefficients.

    A mixed real/imaginary PSLQ basis avoids relations confined to the real or
    imaginary trigonometric subspaces.  This is high-precision numerical
    identification, not a directed-rounding proof.
    """
    tol = mp.power(10, -dps + 12)
    if abs(z) < tol:
        return Cyc(N)
    d = N // 2
    for k in range(N):
        w = z / mp.exp(2j * mp.pi * k / N)
        if abs(mp.im(w)) > tol:
            continue
        x = mp.re(w)
        f = Fraction(mp.nstr(x, dps + 10)).limit_denominator(denominator)
        if abs(x - mp.mpf(f.numerator) / f.denominator) < tol:
            return Cyc(N, {k: f})
    # The full complex cyclotomic basis is Q-linearly independent.  Mixing its
    # real and imaginary parts with pi prevents PSLQ from finding a relation
    # confined to either smaller real trigonometric span.
    basis = [mp.re(mp.exp(2j * mp.pi * k / N)) +
             mp.pi * mp.im(mp.exp(2j * mp.pi * k / N)) for k in range(d)]
    target = mp.re(z) + mp.pi * mp.im(z)
    permutations = [tuple(range(d)), tuple(reversed(range(d)))]
    permutations += [tuple(range(s, d)) + tuple(range(s)) for s in range(1, d)]
    for perm in permutations:
        relation = mp.pslq([basis[k] for k in perm] + [target],
                           tol=mp.power(10, -dps + 15),
                           maxcoeff=denominator, maxsteps=100000)
        if relation is None or not relation[-1]:
            continue
        out = Cyc(N, {k: Fraction(-relation[pos], relation[-1])
                     for pos, k in enumerate(perm) if relation[pos]})
        if out and abs(out.numeric(dps) - z) < mp.power(10, -dps + 8):
            return out
    raise ValueError(f"cyclotomic identification failed for {z}")
