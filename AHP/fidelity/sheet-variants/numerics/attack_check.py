#!/usr/bin/env python3
"""Independent attack checks for AHP/fidelity/sheet-variants.

Re-derives the design's claims from SPEC.md without importing the design
script. Covers the places where SPEC.md states numbers the design script
never computed (the Omega_1 = [0,4)^3 reading-B block), and strengthens two
weak checks (the global-gauge impossibility was only shown for one gauge;
the Pauli frobSq values were a hardcoded dict).

Numerical output is evidence, not a proof. Sides at most 8. Exact integer
arithmetic throughout (complex entries as Gaussian-integer pairs).

Operators transcribed (same sources as the design):
  pcd / pdist            ZStatementP428.lean:58-67
  Om0Print / Om0Rad      RB1.lean:59-60, RB2.lean:26-27 (eq_rad: RB2.lean:29-31)
  Om0Unit                RB2.lean:41-42
  Collar0                RB2.lean:45-46
  Admissible conjuncts   ZStatementP428.lean:73-83
  gauge step             ClayStatement.lean:1312-1316
  frobSq vs ||.||^2      RMapLipschitz.lean:60, :145
  Pauli generators       SuTwoInner.lean:505-523
  unit embedding         ZStatementP428.lean:189-195
"""

from __future__ import annotations

SIDE = 8


def pcd(N: int, a: int, b: int) -> int:
    d = abs(a - b)
    return min(d, N - d)


def sites(side: int):
    return [(a, b, c) for a in range(side) for b in range(side) for c in range(side)]


# Full distance matrix on the side-8 torus, computed once.
S8 = sites(SIDE)
IDX = {x: i for i, x in enumerate(S8)}


def pdist(side: int, x, y) -> int:
    return sum(pcd(side, x[i], y[i]) for i in range(3))


D = [[pdist(SIDE, x, y) for y in S8] for x in S8]


def dmat(x, y) -> int:
    return D[IDX[x]][IDX[y]]


def block_id(s: int, x):
    return tuple(c // s for c in x)


def om0_rad(side: int, s: int, rho: int, om1: set) -> set:
    """Om0Rad s rho Om1 (RB2.lean:26-27): union of s-blocks A with
    SetDistLe A Om1 rho (RB1.lean:38), transcribed via block ids."""
    ids = set()
    for x in sites(side):
        if any(dmat(x, y) <= rho for y in om1):
            ids.add(block_id(s, x))
    return {x for x in sites(side) if block_id(s, x) in ids}


def report(name: str, ok: bool, detail: str) -> bool:
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    return ok


def check_block_om1_numbers():
    """SPEC Q3 vacuity paragraph states |Om0Unit|=512, |Om0Print|=448 and
    min complement distance 3 for Om1 = [0,4)^3 at ell=M=2, R=k=1, side 8.
    The design script never computes these. Verify them here."""
    print("\n== attack 1: Om1 = [0,4)^3 numbers stated in SPEC but not in the design script ==")
    om1 = {x for x in S8 if all(c < 4 for c in x)}
    assert len(om1) == 64
    print_set = om0_rad(SIDE, 2, 2, om1)            # Om0Print 2 1 (RB1.lean:59)
    unit_set = om0_rad(SIDE, 4, 4, om1)             # Om0Unit 2 2 1 1 (RB2.lean:41)
    comp = [x for x in S8 if x not in print_set]
    md = min(dmat(x, y) for x in comp for y in om1) if comp else None
    ok = True
    ok &= report("block-om1-print-448", len(print_set) == 448, f"|Om0Print|={len(print_set)}")
    ok &= report("block-om1-unit-512", len(unit_set) == 512, f"|Om0Unit|={len(unit_set)}")
    ok &= report("block-om1-mindist-3", md == 3, f"min dist(complement of Om0Print, Om1)={md}")
    ok &= report(
        "block-om1-subset-both",
        om1 <= print_set and om1 <= unit_set,
        "Om1 sits in both printed and reading-B sets (om1_sub_om0Print direction)",
    )
    # The excluded blocks should be exactly those with >= 2 coordinates >= 2.
    excluded_ids = {block_id(2, x) for x in comp}
    expect = {b for b in excluded_ids}  # shape check below
    shape = all(sum(1 for c in b if c >= 2) >= 2 for b in excluded_ids) and len(excluded_ids) == 8
    ok &= report(
        "block-om1-excluded-shape",
        shape,
        f"{len(excluded_ids)} side-2 blocks excluded, all with >=2 block-coordinates >= 2",
    )
    return ok


def check_no_proper_readingB_side8():
    """SPEC claims: at headline sizes (ell=2, M=2, k=1) on side 8, 'every
    side-4 block meets the radius-4 neighbourhood of a nonempty Om1', so no
    proper Om0Unit occurs at R >= 1. Taken literally for an ARBITRARY
    nonempty Om1 this is false: the single site (5,5,5) is at distance 6
    from the block [0,4)^3. The claim is only true -- and only needed --
    for Om1 that is a union of side-4 blocks, which is what AdmNoBase
    (THL2.lean:23, BlockClosed conjunct) requires of Om1 at k=1. Check
    both directions: the counterexample for arbitrary Om1, and the
    qualified claim for all 255 nonempty side-4-block unions."""
    print("\n== attack 2: no proper reading-B Omega_0 at headline sizes on side 8 ==")
    blocks = {}
    for x in S8:
        blocks.setdefault(block_id(4, x), []).append(x)
    # (a) unqualified form is false
    y = (5, 5, 5)
    m = min(dmat(z, y) for z in blocks[(0, 0, 0)])
    ok = report(
        "unqualified-form-false",
        m == 6,
        f"min dist(block [0,4)^3, site (5,5,5)) = {m} > 4: SPEC's sentence needs Om1 block-closed",
    )
    # (b) qualified form: block-to-block max min-distance <= 3, exhaustive
    worst = 0
    arg = None
    ids = sorted(blocks)
    for b in ids:
        for b2 in ids:
            m2 = min(dmat(z, y2) for z in blocks[b] for y2 in blocks[b2])
            if m2 > worst:
                worst, arg = m2, (b, b2)
    ok &= report(
        "block-to-block-max-min-dist-le-3",
        worst <= 3,
        f"max over side-4 block pairs of min dist = {worst} at {arg}; radius 4R >= 4 for R >= 1",
    )
    # (c) direct sweep: Om0Unit is the whole torus for every nonempty union
    full = 0
    for mask in range(1, 1 << 8):
        om1 = set()
        for i, b in enumerate(ids):
            if mask >> i & 1:
                om1.update(blocks[b])
        if len(om0_rad(SIDE, 4, 4, om1)) == SIDE ** 3:
            full += 1
    ok &= report(
        "om0unit-full-for-all-255-block-unions",
        full == 255,
        f"Om0Unit(s=4, rho=4) is the whole torus for {full}/255 nonempty side-4-block unions",
    )
    return ok


def check_headline_parameter_enumeration():
    """SPEC says the smallest headline parameters with k >= 2 are ell=2, M=2,
    k=2. Strengthen: enumerate every (ell, m, k, side) with m >= 1, k >= 2,
    side in {4, 8} that satisfies TorusOK and the Admissible divisibility
    conjunct, i.e. that can host any admissible tower at all."""
    print("\n== attack 3: headline (ell, M=ell^m, k>=2) cases fittable on side <= 8 ==")
    fits = []
    for side in (4, 8):
        for ell in range(2, 10):
            for m in range(1, 6):
                M = ell ** m
                for k in range(2, 6):
                    big_k = M * ell ** k
                    # TorusOK (ZStatementP428.lean:286-289): ell | side, ell < side, M | side
                    torus_ok = side % ell == 0 and ell < side and side % M == 0
                    # Admissible divisibility (line 76): bigSide(j) | side for j <= k;
                    # bigSide is nondecreasing in j, so bigSide(k) | side suffices given
                    # bigSide(j) | bigSide(k).
                    divides = big_k <= side and side % big_k == 0 and all(
                        side % (M * ell ** j) == 0 for j in range(k + 1)
                    )
                    if torus_ok and divides:
                        fits.append((side, ell, M, k, big_k))
    ok = True
    ok &= report(
        "only-fit-is-2-2-2-on-8",
        fits == [(8, 2, 2, 2, 8)],
        f"fittable (side, ell, M, k, bigSide(k)) = {fits}; "
        "at the only fit bigSide(k) equals the side, so a block-closed Omega_k is empty or the torus",
    )
    return ok


# --- gauge group {+-I}, independent implementation -------------------------

I2 = ((1, 0), (0, 1))
MI = ((-1, 0), (0, -1))


def mm(A, B):
    return (
        (A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
        (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]),
    )


def check_gauge_exhaustive():
    """Design checked global-gauge impossibility only by propagating one
    gauge and conjugating by g0 = I. Check all 2^4 gauges in {+-I}^4:
    none flattens every link of the 4-cycle with links I, I, I, -I.
    Gauge law: ClayStatement.lean:1312-1316, g(x) U g(x+mu)^{-1}; +-I is
    self-inverse."""
    print("\n== attack 4: exhaustive global-gauge impossibility on the 4-cycle ==")
    U = [I2, I2, I2, MI]
    N = 4
    import itertools

    none_flatten = True
    for bits in itertools.product((0, 1), repeat=4):
        g = [MI if b else I2 for b in bits]
        gauged = [mm(mm(g[i], U[i]), g[(i + 1) % N]) for i in range(N)]
        if all(gl == I2 for gl in gauged):
            none_flatten = False
    # holonomy of every gauged configuration equals g0 * (-I) * g0^{-1} = -I
    hol_ok = True
    for bits in itertools.product((0, 1), repeat=4):
        g = [MI if b else I2 for b in bits]
        gauged = [mm(mm(g[i], U[i]), g[(i + 1) % N]) for i in range(N)]
        H = I2
        for L in gauged:
            H = mm(H, L)
        if H != MI:
            hol_ok = False
    # per-arc flattening, recomputed independently: arc (a, a+1) flattened by
    # g_a = I, g_{a+1} = U_a, g_{a+2} = U_{a+1} U_a applied on the right inverses.
    per_arc = True
    for a in range(N):
        g = [I2, I2, I2, I2]
        g[(a + 1) % N] = mm(g[a], U[a])
        g[(a + 2) % N] = mm(g[(a + 1) % N], U[(a + 1) % N])
        gauged = [mm(mm(g[i], U[i]), g[(i + 1) % N]) for i in range(N)]
        if not (gauged[a] == I2 and gauged[(a + 1) % N] == I2):
            per_arc = False
    ok = True
    ok &= report("no-global-gauge-flattens", none_flatten, "all 16 gauges in {+-I}^4 leave a non-identity link")
    ok &= report("gauged-holonomy-always-minus-I", hol_ok, "all 16 gauged holonomies equal -I")
    ok &= report("per-arc-gauges-exist", per_arc, "each of the 4 two-bond arcs flattens independently")
    return ok


def check_pauli_entrywise():
    """Design's Pauli check was a hardcoded dict. Compute frobSq entrywise
    from the definitions pauliE1Val = !![0,i;i,0] (SuTwoInner.lean:505-506),
    E2 = !![0,1;-1,0] (:518-520), E3 = !![i,0;0,-i] (:522-523), and
    cross-check the (a,b,c) family with explicit complex entries."""
    print("\n== attack 5: Pauli frobSq entrywise, and the family with explicit entries ==")

    def entrywise_frob(X):  # X: 2x2 of (re, im)
        return sum(re * re + im * im for row in X for (re, im) in row)

    Ip = (0, 1)
    one = (1, 0)
    zero = (0, 0)
    E1 = ((zero, Ip), (Ip, zero))
    E2 = ((zero, one), (( -1, 0), zero))
    E3 = ((Ip, zero), (zero, (0, -1)))
    ok = True
    for name, E in (("E1", E1), ("E2", E2), ("E3", E3)):
        f = entrywise_frob(E)
        ok &= report(f"pauli-{name}-frobSq-2", f == 2 and f % 2 == 0, f"frobSq({name})={f}, half={f//2}")

    def family(a, b, c):
        # X = [[i a, b + i c], [-b + i c, -i a]] with explicit entries
        return (((0, a), (b, c)), ((-b, c), (0, -a)))

    fam_ok = True
    for (a, b, c) in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (2, -3, 5), (0, 0, 0), (1, 1, 1), (-4, 7, -2)]:
        f = entrywise_frob(family(a, b, c))
        if f != 2 * (a * a + b * b + c * c):
            fam_ok = False
    ok &= report("family-entrywise-factor-2", fam_ok, "frobSq = 2(a^2+b^2+c^2) on 7 explicit-entry samples")
    return ok


def check_embedding_second_parameters():
    """Design checked pdist scaling only at (ell,k,unit)=(2,1,4). Add
    (3,1,2) -> fine 6 and (2,2,2) -> fine 8 (fine side still <= 8)."""
    print("\n== attack 6: embedding identity at two more parameter sets ==")
    ok = True
    for ell, k, unit in ((3, 1, 2), (2, 2, 2)):
        e = ell ** k
        fine = unit * e
        bad = 0
        n = 0
        for y in sites(unit):
            for z in sites(unit):
                ey = tuple(e * c for c in y)
                ez = tuple(e * c for c in z)
                n += 1
                if pdist(fine, ey, ez) != e * pdist(unit, y, z):
                    bad += 1
        ok &= report(
            f"emb-scales-ell{ell}-k{k}",
            bad == 0,
            f"{n} pairs on unit side {unit}, fine side {fine}, mismatches={bad}",
        )
    return ok


def check_separator_independent():
    """Re-derive the Q2(b) M=1 separator with a fresh construction, and
    verify the equality-at-distance-2 witness is the ONLY reason strict
    fails (min over comp(Om1) x Om2 is exactly 2, attained)."""
    print("\n== attack 7: collar separator, independent construction ==")
    side, ell, M, R, k = 8, 2, 1, 1, 2
    om2 = {(a, b, c) for a in range(4) for b in range(4) for c in range(4)}
    hole = {(a, b, c) for a in range(4, 6) for b in range(4, 6) for c in range(2)}
    om1 = set(S8) - hole
    om0 = set(S8)
    om = {0: om0, 1: om1, 2: om2, 3: set(), 4: set()}

    def big(j):
        return M * ell ** j

    nesting = all(om[j + 1] <= om[j] for j in range(4))
    above = om[3] == set() and om[4] == set()
    divides = all(side % big(j) == 0 for j in range(3))
    closed = True
    for j in range(3):
        ids = {block_id(big(j), x) for x in om[j]}
        if {x for x in S8 if block_id(big(j), x) in ids} != om[j]:
            closed = False
    # clause 6 (M=1, R=1): Om0 = sites within distance 1 of Om1
    clause6 = om0 == {x for x in S8 if any(dmat(x, y) <= 1 for y in om1)}
    # collars, with the exact distribution of distances at j=1
    dists = [dmat(x, y) for x in S8 if x not in om1 for y in om2]
    mn = min(dists)
    eq_witnesses = [(x, y) for x in S8 if x not in om1 for y in om2 if dmat(x, y) == R * big(1)]
    strict_j1 = all(dmat(x, y) > R * big(1) for x in S8 if x not in om1 for y in om2)
    nonstrict_j1 = mn >= R * big(1)
    ok = True
    ok &= report(
        "sep-conjuncts",
        nesting and above and divides and closed and clause6,
        f"nesting={nesting} above={above} divides={divides} closed={closed} clause6={clause6}",
    )
    ok &= report(
        "sep-collar-equality-only",
        (not strict_j1) and nonstrict_j1 and mn == 2 and len(eq_witnesses) > 0,
        f"min dist over comp(Om1) x Om2 = {mn} = R*bigSide(1) = {R*big(1)}; "
        f"{len(eq_witnesses)} equality pairs, e.g. {eq_witnesses[0]}; strict fails only by equality",
    )
    return ok


def check_k1_agreement_sweep():
    """SPEC: at k=1, towers keeping clause 6 have the strict and non-strict
    collar predicates agree (level-1 collar vacuous since Om2 = empty;
    level-0 collar forced strict by om0Print_collar, RB2.lean:76). Sweep
    all 256 unions Om1 of side-4 blocks at ell=2, M=2, R=1, side 8, and a
    seeded sample of 300 side-2-block unions at M=1."""
    print("\n== attack 8: k=1 strict/non-strict agreement sweep (evidence for SPEC's k=1 claim) ==")
    ok = True

    def collars_agree(M, R, om1):
        om0 = om0_rad(SIDE, M, R * M, om1)  # clause-6-forced Omega_0 (om0Print_eq_rad)
        # j = 0 collar against Om1; j = 1 collar vacuous (Om2 = empty)
        strict = all(dmat(x, y) > R * M for x in S8 if x not in om0 for y in om1)
        nonstrict = all(dmat(x, y) >= R * M for x in S8 if x not in om0 for y in om1)
        return strict == nonstrict, strict

    blocks4 = sorted({block_id(4, x) for x in S8})
    sites_of4 = {b: [x for x in S8 if block_id(4, x) == b] for b in blocks4}
    n_bad = 0
    n_strict = 0
    for mask in range(1, 1 << 8):
        om1 = set()
        for i, b in enumerate(blocks4):
            if mask >> i & 1:
                om1.update(sites_of4[b])
        agree, strict = collars_agree(2, 1, om1)
        n_strict += strict
        if not agree:
            n_bad += 1
    ok &= report(
        "k1-sweep-M2-all-256",
        n_bad == 0 and n_strict == 255,
        f"256 nonempty side-4-block unions: disagreements={n_bad}, strict collar held in {n_strict}/255 "
        "(full-torus Om1 gives an empty complement, also strict)",
    )
    import random

    rng = random.Random(20261020)
    blocks2 = sorted({block_id(2, x) for x in S8})
    sites_of2 = {b: [x for x in S8 if block_id(2, x) == b] for b in blocks2}
    n_bad = 0
    for _ in range(300):
        om1 = set()
        for b in blocks2:
            if rng.random() < 0.3:
                om1.update(sites_of2[b])
        if not om1:
            continue
        agree, _ = collars_agree(1, 1, om1)
        if not agree:
            n_bad += 1
    ok &= report("k1-sweep-M1-sample-300", n_bad == 0, f"300 seeded side-2-block unions at M=1: disagreements={n_bad}")
    return ok


def check_quantifier_toy_second_window():
    """Re-run the Q13 binder-shape toy with different windows."""
    print("\n== attack 9: Q13 toy, second window ==")

    def frozen(m_max, w):
        for m in range(1, m_max):
            R0 = m
            if any(R < m for R in range(R0, R0 + w)):
                return False
        return True

    def total(m_max, w, r1_max):
        for m1 in range(1, m_max):
            for R1 in range(0, r1_max):
                if all(R >= m for m in range(m1, m_max) for R in range(R1, R1 + w)):
                    return True
        return False

    f = frozen(60, 4)
    t = total(60, 4, 20)
    ok = report(
        "toy-window-2",
        f and not t,
        f"m<60, window 4, R1<20: frozen-shape={f}, total-shape={t} (toy, not the coercivity predicate)",
    )
    return ok


def main():
    results = [
        check_block_om1_numbers(),
        check_no_proper_readingB_side8(),
        check_headline_parameter_enumeration(),
        check_gauge_exhaustive(),
        check_pauli_entrywise(),
        check_embedding_second_parameters(),
        check_separator_independent(),
        check_k1_agreement_sweep(),
        check_quantifier_toy_second_window(),
    ]
    print("\n== attack summary ==")
    print("all_checks", all(results), "n", len(results))
    if not all(results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
