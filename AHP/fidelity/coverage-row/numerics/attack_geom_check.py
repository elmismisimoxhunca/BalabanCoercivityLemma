#!/usr/bin/env python3
"""ATTACK-side check: the neS witness tower has a nonempty, proper Omega_0.

extent_check.py only transcribes extent formulas. It never checks that the
tower the ell=2 witness lives on has 0 < |Omega_0| < torus, or that the
slab coordinates satisfy the arithmetic the Admissible proof needs. This
script fills that gap, as evidence, not a proof.

Transcribed definitions (integer formulas only; no operators):

- tw3 (NsCvNe1.lean:23-25): Omega_0 = {x : P0 <= x_0 < Q0}, a slab in
  direction 0; Omega_1 = [P1,Q1); Omega_2 = [A',B') ∪ [A,B).
- neS (NsCvNe2.lean:122-124): tw3 with P0=neP0, Q0=neQ0, P1=neP1,
  Q1=neQ1, A'=neA', B'=neB', A=neA, B=neB.
- neP1 = neA' - ell*(R*M)          (NsCvNe2.lean:111)
- neQ1 = neB + ell*(R*M)           (NsCvNe2.lean:112)
- neP0 = neP1 - R*M                (NsCvNe2.lean:113)
- neQ0 = neQ1 + R*M                (NsCvNe2.lean:114)
- neA  = ell*(ell*(R*M)) + cf*(ell*(ell*M)) + ell*(ell*M)   (:109)
- neB  = 3*(ell*(ell*(R*M))) + cf*(ell*(ell*M)) + 4*(ell*(ell*M))  (:110)
- neA', neB', neNu, neN as in extent_check.py (:105,:107,:108,:115).
- Geo3 (NsCvNe1.lean:48-71): the arithmetic clauses tw3_admissible needs.
  Checked here: w2, gap, w2', QN, d0, d1, d2, b0P..b2B, cP, cQ, cP2, cQ2.

A numerical result is evidence about these integers, not a proof.
"""

from __future__ import annotations


def neNu(M: int, R: int, cf: int) -> int:  # NsCvNe2.lean:105
    return 4 * (R * M) + 2 * (cf * M) + 6 * M


def neA_prime(ell: int, M: int, R: int) -> int:  # NsCvNe2.lean:107
    return ell * (ell * (R * M)) + ell * (ell * M)


def neB_prime(ell: int, M: int, R: int, cf: int) -> int:  # NsCvNe2.lean:108
    return ell * (ell * (R * M)) + cf * (ell * (ell * M))


def neA(ell: int, M: int, R: int, cf: int) -> int:  # NsCvNe2.lean:109
    return ell * (ell * (R * M)) + cf * (ell * (ell * M)) + ell * (ell * M)


def neB(ell: int, M: int, R: int, cf: int) -> int:  # NsCvNe2.lean:110
    return (
        3 * (ell * (ell * (R * M)))
        + cf * (ell * (ell * M))
        + 4 * (ell * (ell * M))
    )


def neN(ell: int, M: int, R: int, cf: int) -> int:  # NsCvNe2.lean:115
    return (
        4 * (ell * (ell * (R * M)))
        + 2 * (cf * (ell * (ell * M)))
        + 6 * (ell * (ell * M))
    )


def coords(ell: int, M: int, R: int, cf: int) -> dict[str, int]:
    ap = neA_prime(ell, M, R)
    p1 = ap - ell * (R * M)  # neP1, :111
    b = neB(ell, M, R, cf)
    q1 = b + ell * (R * M)  # neQ1, :112
    return {
        "P0": p1 - R * M,  # neP0, :113
        "Q0": q1 + R * M,  # neQ0, :114
        "P1": p1,
        "Q1": q1,
        "Ap": ap,
        "Bp": neB_prime(ell, M, R, cf),
        "A": neA(ell, M, R, cf),
        "B": b,
        "N": neN(ell, M, R, cf),
        "Nu": neNu(M, R, cf),
    }


def geo3_holds(ell: int, M: int, R: int, cf: int) -> bool:
    c = coords(ell, M, R, cf)
    P0, Q0, P1, Q1 = c["P0"], c["Q0"], c["P1"], c["Q1"]
    Ap, Bp, A, B, N = c["Ap"], c["Bp"], c["A"], c["B"], c["N"]
    checks = [
        0 < M, 0 < ell,  # hM, hell
        Ap < Bp,  # w2
        Bp <= A,  # gap
        A < B,  # w2'
        Q0 <= N,  # QN
        N % M == 0,  # d0
        N % (M * ell) == 0,  # d1
        N % (M * ell**2) == 0,  # d2
        P0 % M == 0,  # b0P
        Q0 % M == 0,  # b0Q
        P1 % (M * ell) == 0,  # b1P
        Q1 % (M * ell) == 0,  # b1Q
        Ap % (M * ell**2) == 0,  # b2A'
        Bp % (M * ell**2) == 0,  # b2B'
        A % (M * ell**2) == 0,  # b2A
        B % (M * ell**2) == 0,  # b2B
        P1 == P0 + R * M,  # cP
        Q0 == Q1 + R * M,  # cQ
        Ap == P1 + R * (M * ell),  # cP2
        Q1 == B + R * (M * ell),  # cQ2
        # nesting of the slabs (from the definitions, needed for a tower)
        P0 <= P1 and Q1 <= Q0,
        P1 <= Ap and B <= Q1,  # Omega_2 inside Omega_1
    ]
    return all(checks)


def main() -> None:
    ell = 2
    rows = {
        "formula_min_cf10": (2, 1, 1, 10),  # not a witness of the declaration (m = 0)
        "failEllCS_two_smallest": (2, 4, 1, 10),  # m = 2, R = 1 (NuA1.lean:44-53)
        "constFam_witness_two_R_ge_c": (2, 4, 10, 10),  # R >= c (NuA3.lean:103-105)
    }
    grid_checked = 0
    for M in range(1, 5):
        for R in (1, 10, 21):
            for cf in (10, 12, 16):
                assert geo3_holds(ell, M, R, cf)
                c = coords(ell, M, R, cf)
                assert 0 < c["Q0"] - c["P0"] < c["N"]  # Omega_0 nonempty and proper
                grid_checked += 1
    print(f"geo3_grid_checks {grid_checked} (M in 1..4, R in (1,10,21), cf in (10,12,16), ell=2)")
    for name, (ell_, M, R, cf) in rows.items():
        c = coords(ell_, M, R, cf)
        om0_width = c["Q0"] - c["P0"]
        print(
            f"{name} P0={c['P0']} Q0={c['Q0']} N={c['N']} "
            f"om0_width={om0_width} nonempty={om0_width > 0} "
            f"proper={om0_width < c['N']} geo3={geo3_holds(ell_, M, R, cf)}"
        )
    print("note nonempty/proper Omega_0 is also a consequence of the committed")
    print("Admissible proof (ne_admissible_two); this script is evidence only")
    print("operator_modelled no")


if __name__ == "__main__":
    main()
