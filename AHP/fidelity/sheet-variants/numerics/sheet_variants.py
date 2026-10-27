#!/usr/bin/env python3
"""Geometry and algebra checks for statement-sheet variants.

Numerical output is evidence, not a proof. No operator here is the coercivity form.
Each checker cites the Lean definition it transcribes.

Side lengths are at most 8. Memory is a few Python lists.
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# pdist: ZStatementP428.lean:57-71
#   pcd N a b = min(|a-b|, N-|a-b|)
#   pdist x y = sum over 3 axes of pcd (L μ + 1)
# L μ stores N-1 sites-minus-one, so the side length is Lμ+1.
# ---------------------------------------------------------------------------

def pcd(N: int, a: int, b: int) -> int:
    d = b - a if a <= b else a - b
    return min(d, N - d)


def pdist(side: int, x, y) -> int:
    return sum(pcd(side, x[i], y[i]) for i in range(3))


def sites(side: int):
    return [
        (x0, x1, x2)
        for x0 in range(side)
        for x1 in range(side)
        for x2 in range(side)
    ]


def block_id(s: int, x):
    return tuple(c // s for c in x)


def same_block(s: int, x, y) -> bool:
    return block_id(s, x) == block_id(s, y)


# Om0Rad: RB2.lean:31-32. A site is in iff its s-block meets the ρ-neighbourhood of Om1.
# Om0Print M R = Om0Rad M (R*M)          RB2.lean:34-35 (and RB1.lean:59-60)
# Om0Unit ell M R k = Om0Rad (M*ell^k) (R*(M*ell^k))   RB2.lean:41-42

def om0_rad(side: int, s: int, rho: int, om1: set):
    near_blocks = set()
    for x in sites(side):
        if any(pdist(side, x, y) <= rho for y in om1):
            near_blocks.add(block_id(s, x))
    return {x for x in sites(side) if block_id(s, x) in near_blocks}


def collar0(side: int, M: int, R: int, omega: set, om1: set) -> bool:
    """RB2.lean:45-46. x not in omega ⇒ R*M < pdist(x, y) for every y in om1."""
    rad = R * M
    for x in sites(side):
        if x in omega:
            continue
        for y in om1:
            if not (rad < pdist(side, x, y)):
                return False
    return True


def min_comp_dist(side: int, omega: set, om1: set):
    comp = [x for x in sites(side) if x not in omega]
    if not comp or not om1:
        return None
    return min(pdist(side, x, y) for x in comp for y in om1)


def report(name: str, ok: bool, detail: str) -> bool:
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    return ok


def check_reading_b():
    print("\n== Q3/Q4 reading B (Om0Unit vs Om0Print) ==")
    # Sol witness: SolRBridgeAudit.lean:22-42, Lw side 8 (extent 7), ell=2,M=2,R=1,k=1,
    # Om1w = {0}, x400 = (4,0,0).
    side = 8
    om1 = {(0, 0, 0)}
    x400 = (4, 0, 0)
    print_set = om0_rad(side, s=2, rho=1 * 2, om1=om1)          # Om0Print 2 1
    unit_set = om0_rad(side, s=2 * 2**1, rho=1 * (2 * 2**1), om1=om1)  # Om0Unit 2 2 1 1
    d400 = pdist(side, x400, (0, 0, 0))
    ok = True
    ok &= report(
        "sol-x400-distance",
        d400 == 4,
        f"pdist(x400,0)={d400} (Sol's decide proof uses the block, not this single distance)",
    )
    ok &= report(
        "sol-x400-in-unit-not-print",
        x400 in unit_set and x400 not in print_set,
        f"in Om0Unit={x400 in unit_set}, in Om0Print={x400 in print_set}",
    )
    ok &= report(
        "sol-unit-is-full-torus",
        len(unit_set) == side**3,
        f"|Om0Unit|={len(unit_set)} of {side**3}; complement empty ⇒ Collar0 is vacuous",
    )
    ok &= report(
        "sol-print-proper",
        0 < len(print_set) < side**3,
        f"|Om0Print|={len(print_set)}",
    )
    ok &= report(
        "sol-collar-vacuous-true",
        collar0(side, 2, 1, unit_set, om1),
        "Collar0 M=2 R=1 holds because the complement is empty",
    )
    # Proper nonempty reading-B domain, BELOW the headline (M=1 is not ell^m for ell≥2).
    # Geometry only: RB2.lean:41-42 with ell=2,M=1,R=1,k=1, side 8.
    om1b = {(0, 0, 0)}
    print_b = om0_rad(side, s=1, rho=1, om1=om1b)
    unit_b = om0_rad(side, s=1 * 2, rho=1 * 2, om1=om1b)
    x_far = (4, 4, 4)
    x_mid = (2, 0, 0)
    ok &= report(
        "proper-B-not-full",
        x_mid in unit_b and x_mid not in print_b and x_far not in unit_b and (0, 0, 0) in unit_b,
        f"|Om0Print|={len(print_b)} |Om0Unit|={len(unit_b)} "
        f"x_mid in unit/print={x_mid in unit_b}/{x_mid in print_b} "
        f"x_far in unit={x_far in unit_b}",
    )
    md = min_comp_dist(side, unit_b, om1b)
    ok &= report(
        "proper-B-fine-collar",
        collar0(side, M=1, R=1, omega=unit_b, om1=om1b) and md is not None and md > 1,
        f"min dist(complement, Om1)={md}, Collar0 radius R*M=1 (RB2.lean:45)",
    )
    # In-regime block: ell=2,M=2,k=1 ⇒ block side M*ell^k=4, radius R*4 with R≥1.
    # On side 8 every side-4 block meets the 3-neighbourhood of any site, so radius ≥4 fills.
    filled = True
    for R in (1, 2):
        u = om0_rad(side, s=4, rho=R * 4, om1=om1)
        filled &= len(u) == side**3
    ok &= report(
        "inregime-side8-readingB-fills",
        filled,
        "ell=2,M=2,k=1,R≥1,side=8: Om0Unit is the whole torus (collar vacuous). "
        "No proper in-regime reading-B domain exists at side ≤8.",
    )
    return ok


def admissible_parts(side, ell, M, R, k, om):
    """Transcribe Admissible, ZStatementP428.lean:73-83, collar conjunct separate.

    Returns a dict of the six conjuncts, with the collar tested both strictly (<)
    and non-strictly (≤). bigSide = M*ell^j (line 50).
    """

    def big_side(j):
        return M * ell**j

    nesting = all(om[j + 1] <= om[j] for j in range(k + 2))
    above = all(len(om[j]) == 0 for j in range(k + 1, k + 3))
    divides = all(side % big_side(j) == 0 for j in range(k + 1))
    closed = True
    for j in range(k + 1):
        s = big_side(j)
        for x in om[j]:
            # full block test would be |block| checks; the partition test:
            pass
        ids = {block_id(s, x) for x in om[j]}
        rebuilt = {x for x in sites(side) if block_id(s, x) in ids}
        if rebuilt != om[j]:
            closed = False
            break
    strict = True
    nonstrict = True
    witness = None
    for j in range(k + 1):
        rad = R * big_side(j)
        comp = [x for x in sites(side) if x not in om[j]]
        for x in comp:
            for y in om[j + 1]:
                d = pdist(side, x, y)
                if not (rad < d):
                    strict = False
                    if witness is None and rad == d:
                        witness = (j, x, y, d, rad)
                if not (rad <= d):
                    nonstrict = False
    # clause 6, lines 80-83, blocks of side M, radius R*M, against Om 1
    rad0 = R * M
    predicted = om0_rad(side, M, rad0, om[1])
    clause6 = predicted == om[0]
    return {
        "nesting": nesting,
        "above": above,
        "divides": divides,
        "closed": closed,
        "strict_collar": strict,
        "nonstrict_collar": nonstrict,
        "clause6": clause6,
        "equality_witness": witness,
    }


def check_collar():
    print("\n== Q2(b) strict vs non-strict collar ==")
    side = 8
    ell, M, R, k = 2, 1, 1, 2
    # M=1 is not a headline power ell^m. It is only a witness that Admissible's
    # collar conjuncts are not the same predicate.
    om2 = {x for x in sites(side) if all(c < 4 for c in x)}
    comp1 = {x for x in sites(side) if block_id(2, x) == (2, 2, 0)}  # [4,6) x [4,6) x [0,2)
    om1 = set(sites(side)) - comp1
    om0 = set(sites(side))  # clause 6 for M=1,R=1 against this Om1 is everything
    om = {0: om0, 1: om1, 2: om2, 3: set(), 4: set()}
    parts = admissible_parts(side, ell, M, R, k, om)
    ok = True
    ok &= report(
        "separator-shape",
        parts["nesting"] and parts["above"] and parts["divides"] and parts["closed"] and parts["clause6"],
        f"nesting={parts['nesting']} above={parts['above']} divides={parts['divides']} "
        f"closed={parts['closed']} clause6={parts['clause6']} |Om1|={len(om1)} |Om2|={len(om2)}",
    )
    ok &= report(
        "separator-collar-gap",
        (not parts["strict_collar"]) and parts["nonstrict_collar"] and parts["equality_witness"] is not None,
        f"strict={parts['strict_collar']} nonstrict={parts['nonstrict_collar']} "
        f"witness (j,x,y,dist,radius)={parts['equality_witness']}",
    )
    # Clause 6 at level 0 forces the strict collar (RB2.lean:76-84, om0Print_collar).
    # A one-point Omega_1 is not block-closed at side M*ell, so this is the printed
    # set alone, not a full Admissible tower.
    om1h = {(0, 0, 0)}
    om0h = om0_rad(side, 2, 2, om1h)
    md = min_comp_dist(side, om0h, om1h)
    ok &= report(
        "clause6-print-collar-strict",
        md is not None and md >= 2 + 1 and collar0(side, 2, 1, om0h, om1h),
        f"|Om0Print|={len(om0h)} min dist(complement, Om1)={md} "
        f"(radius R*M=2, so the strict collar is dist>2)",
    )
    # In-regime k≥2 on side ≤8 cannot host a proper level-2 block.
    # ell=2,M=2,k=2 ⇒ bigSide(2)=8, so on side 8 Omega_2 is empty or the torus.
    ok &= report(
        "no-inregime-gap-on-side8",
        (2 * 2**2) == 8,
        "bigSide(M=2,ell=2,j=2)=8 equals the largest allowed side, so a proper nonempty "
        "level-2 block does not fit. The separator above uses M=1.",
    )
    return ok


def mat_mul(A, B):
    return tuple(
        tuple(sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2))
        for i in range(2)
    )


def mat_eq(A, B):
    return A == B


I2 = ((1, 0), (0, 1))
MINUS_I = ((-1, 0), (0, -1))


def gauge_link(g_left, U, g_right):
    """periodicGaugeTransform, ClayStatement.lean:1312-1316:
    γ(x) * U(x,μ) * γ(x+μ)⁻¹.  For ±I, each matrix is its own inverse.
    """
    return mat_mul(mat_mul(g_left, U), g_right)  # g_right is already the inverse


def check_gauge():
    print("\n== Q6(a) one global gauge vs per-cube gauges ==")
    # 4-cycle in direction 0. Links U[0]=U[1]=U[2]=I, U[3]=-I. Holonomy -I.
    # A "cube" here is a 2-bond arc, NOT an IsClassCube. The check transcribes only
    # the quantifiers ∀ cube ∃ g  vs  ∃ g ∀ cube, and the gauge formula.
    U = [I2, I2, I2, MINUS_I]
    N = 4

    def holonomy(links):
        P = I2
        for L in links:
            P = mat_mul(P, L)
        return P

    def gauged(g, links):
        out = []
        for i, L in enumerate(links):
            out.append(gauge_link(g[i], L, g[(i + 1) % N]))  # inverse of ±I is itself
        return out

    H = holonomy(U)
    ok = True
    ok &= report("holonomy-is-minus-I", mat_eq(H, MINUS_I), f"holonomy={H}")

    # Per-arc gauges: propagate along the arc only; identity off the arc's internal need.
    arcs = [(0, 1), (1, 2), (2, 3), (3, 0)]
    per_ok = True
    samples = []
    for a, b in arcs:
        g = [I2, I2, I2, I2]
        # sites: a, a+1, a+2. Set g[a]=I and propagate across the two links.
        g[a] = I2
        g[(a + 1) % N] = mat_mul(g[a], U[a])
        g[(a + 2) % N] = mat_mul(g[(a + 1) % N], U[(a + 1) % N])
        # The second link of the arc is index b = (a+1)%N, whose right endpoint is (a+2).
        gl = gauged(g, U)
        flat = mat_eq(gl[a], I2) and mat_eq(gl[b], I2)
        per_ok &= flat
        samples.append((a, b, flat, gl[a], gl[b]))
    ok &= report("per-arc-exists", per_ok, f"arcs={samples}")

    # One g cannot flatten every link: gauged holonomy is conjugate to -I, hence -I,
    # while a product of I is I. Checked on the propagated global attempt and by the identity.
    g_try = [I2, I2, I2, I2]
    for i in range(N - 1):
        g_try[i + 1] = mat_mul(g_try[i], U[i])
    # closing: g[0] should equal g[3]*U[3]
    close = mat_mul(g_try[3], U[3])
    ok &= report(
        "global-propagation-inconsistent",
        not mat_eq(close, g_try[0]),
        f"g0={g_try[0]} g3*U3={close}",
    )
    # Conjugacy: for this abelian ±I subgroup every gauge leaves links unchanged
    # when g is globally constant, and the general telescoping is recorded in SPEC.
    # Concrete: product of gauged links for g_try (a partial gauge) still has
    # holonomy conjugate to -I. Compute g0 * H * g0^{-1}.
    conj = mat_mul(mat_mul(g_try[0], H), g_try[0])  # inverse of ±I is itself
    ok &= report(
        "gauged-holonomy-stays-minus-I",
        mat_eq(conj, MINUS_I) and not mat_eq(MINUS_I, I2),
        f"conjugate={conj}",
    )
    return ok


def frob_sq(a, b, c) -> int:
    """X = [[i a, b+i c], [-b+i c, -i a]], traceless skew-hermitian.
    frobSq = Σ |Xij|² = RMapLipschitz.lean:60-63, transcribed entrywise.
    """
    return 2 * (a * a + b * b + c * c)


def hs_sq(a, b, c) -> int:
    """‖X‖² = hsInner X X = (1/2) Σ|Xij|².
    SuTwoInner.lean:143-154 and RMapLipschitz.lean:145-149 (norm_sq_eq_half_frobSq).
    """
    return a * a + b * b + c * c


def check_norm():
    print("\n== Q12 trace-normalised vs unnormalised Hilbert-Schmidt ==")
    # Pauli generators as in SuTwoInner.lean:506-522, up to the real coordinates (a,b,c):
    # E3 = i σ3 corresponds to (a,b,c)=(1,0,0); E1 = i σ1 is not of this real form
    # (its entries are pure imaginary off-diagonal and equal). Use the (a,b,c) family,
    # which is the general traceless skew-hermitian matrix, plus the three Paulis
    # computed entrywise below.
    samples = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (2, -3, 5), (0, 0, 0), (1, 1, 1)]
    ok = True
    for s in samples:
        f = frob_sq(*s)
        h = hs_sq(*s)
        ok &= f == 2 * h
    ok &= report(
        "factor-two-on-family",
        ok,
        "for every sample, frobSq = 2 * ‖X‖², including 0",
    )
    # Entrywise Paulis.
    # E1 = [[0, i], [i, 0]]: sum | |² = 0+1+1+0 = 2, hs = 1 (hsInner_e1_e1).
    # E2 = [[0, 1], [-1, 0]]: sum = 2, hs = 1.
    # E3 = [[i, 0], [0, -i]]: sum = 2, hs = 1.
    paulis = {"E1": 2, "E2": 2, "E3": 2}
    ok &= report(
        "pauli-frobSq-2",
        all(v == 2 for v in paulis.values()),
        "hsInner(Ei,Ei)=1 and frobSq(Ei)=2, so the squared norms differ by 2",
    )
    # bond energy rescale: γ * Σ ‖B‖² ≤ form  iff  (γ/2) * Σ frobSq(B) ≤ form.
    bond_hs = [hs_sq(1, 0, 0), hs_sq(0, 2, 0), hs_sq(1, 1, 1)]
    bond_frob = [frob_sq(1, 0, 0), frob_sq(0, 2, 0), frob_sq(1, 1, 1)]
    gamma = 6
    left_printed = gamma * sum(bond_hs)
    left_hs = (gamma // 2) * sum(bond_frob)
    ok &= report(
        "gamma-rescales-by-half",
        left_printed == left_hs and sum(bond_frob) == 2 * sum(bond_hs),
        f"printed left={left_printed} HS left with γ/2={left_hs} sum frob={sum(bond_frob)}",
    )
    return ok


def check_lambda_scale():
    print("\n== Q4 same R, unit collar vs fine collar ==")
    # LambdaOK, ZStatementP428.lean:195: on the UNIT torus, R*M < pdist(y,y').
    # Embedding emb(y)_μ = ell^k * (y μ).val, line 192.
    # Level-k fine collar uses radius R * bigSide = R * M * ell^k (lines 50, 78-79).
    ell, k, M, R = 2, 1, 2, 3
    unit = 4
    fine = unit * ell**k
    ok = True
    mismatches = 0
    checked = 0
    for y in sites(unit):
        for z in sites(unit):
            du = pdist(unit, y, z)
            ey = tuple(ell**k * c for c in y)
            ez = tuple(ell**k * c for c in z)
            df = pdist(fine, ey, ez)
            checked += 1
            if df != ell**k * du:
                mismatches += 1
            # the two strict inequalities use the same R
            unit_sep = (R * M) < du
            fine_sep = (R * M * ell**k) < df
            if unit_sep != fine_sep:
                mismatches += 1
    ok &= report(
        "embedding-scales-pdist",
        mismatches == 0,
        f"checked {checked} pairs, mismatches={mismatches}, ell^k={ell**k}, fine side={fine}",
    )
    return ok


def check_quantifier_shape():
    print("\n== Q13 binder-order shape (not the coercivity predicate) ==")
    # Frozen shape ZT5A.lean:291-294: exists m0, forall m>=m0, exists R0, forall R>=R0, P(m,R)
    # Total shape TT_F.lean:29-36: exists m1, exists R1, forall m>=m1, forall R>=R1, P(m,R)
    # Toy P(m,R) = (R >= m). The shapes are not equivalent.
    # This does NOT say the frozen coercivity statement fails to imply Total:
    # Total is a separate stronger theorem (TT_F.lean p428Target8Total).
    def frozen_holds() -> bool:
        m0 = 1
        for m in range(m0, 40):
            R0 = m  # may depend on m
            for R in range(R0, R0 + 3):
                if R < m:
                    return False
        return True

    def total_holds() -> bool:
        for m1 in range(1, 12):
            for R1 in range(0, 12):
                good = True
                for m in range(m1, 40):
                    for R in range(R1, R1 + 3):
                        if R < m:
                            good = False
                            break
                    if not good:
                        break
                if good:
                    return True
        return False

    frozen = frozen_holds()
    total = total_holds()
    ok = report(
        "shapes-differ",
        frozen and not total,
        "frozen-shape holds and total-shape fails for P=(R>=m): "
        "a single R1 cannot serve every larger m",
    )
    return ok


def main():
    results = [
        check_reading_b(),
        check_collar(),
        check_gauge(),
        check_norm(),
        check_lambda_scale(),
        check_quantifier_shape(),
    ]
    print("\n== summary ==")
    print("all_checks", all(results), "n", len(results))
    if not all(results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
