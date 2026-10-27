#!/usr/bin/env python3
"""Extent arithmetic for the ell=2 nested witness. Not an operator model.

Transcribed definitions (integer formulas only; no genForm, Ginv, or inequality):

- neNu: lean/src/NsCvNe2.lean:105
    4*(R*M) + 2*(cf*M) + 6*M
- neLu: lean/src/NsCvNe2.lean:106
    extent storing neNu - 1, so the unit side is neNu
- neA': lean/src/NsCvNe2.lean:107
    ell*(ell*(R*M)) + ell*(ell*M)
- neN: lean/src/NsCvNe2.lean:115
    4*(ell*(ell*(R*M))) + 2*(cf*(ell*(ell*M))) + 6*(ell*(ell*M))
- scaleUp: lean/src/ZStatementP428.lean:42-43
    fine side = (Lu + 1) * ell^k ; k = 2 on neS (NsCvNe2.lean:122)
- ne_scaleUp: lean/src/NsCvNe2.lean:130-133
    scaleUp ell 2 (neLu) side = neN, and neN = neNu * ell^2
- neC0: lean/src/NuTwoUnc.lean:33
    neA' + cf*(ell*M) - (ell*M + 1)
- docstring identity, NuTwoUnc.lean:32:
    neC0 + 1 = neA' + (cf - 1)*(ell*M)
- thin interval, NuTwoUnc.lean:4-5 and NsCvNe2.lean:108:
    neB' - neA' = (cf - 1)*ell*(ell*M)

CfData.cf >= 10: lean/src/NsCvNe2.lean:31-33.
failEllCS_two constructs m >= 2 and R >= 1: lean/src/NuA1.lean:44-53.
constFam_witness_two chooses R >= c: lean/src/NuA3.lean:99-105 (hRc);
this bound is not a field of the Prop ConstFamWitnessTwo.

A numerical result is evidence about these integers, not a proof.
"""

from __future__ import annotations


def neNu(M: int, R: int, cf: int) -> int:
    # NsCvNe2.lean:105
    return 4 * (R * M) + 2 * (cf * M) + 6 * M


def neA_prime(ell: int, M: int, R: int) -> int:
    # NsCvNe2.lean:107
    return ell * (ell * (R * M)) + ell * (ell * M)


def neB_prime(ell: int, M: int, R: int, cf: int) -> int:
    # NsCvNe2.lean:108
    return ell * (ell * (R * M)) + cf * (ell * (ell * M))


def neN(ell: int, M: int, R: int, cf: int) -> int:
    # NsCvNe2.lean:115
    return (
        4 * (ell * (ell * (R * M)))
        + 2 * (cf * (ell * (ell * M)))
        + 6 * (ell * (ell * M))
    )


def fine_side(ell: int, k: int, unit_side: int) -> int:
    # ZStatementP428.lean:42-43, side = (Lu + 1) * ell^k
    return unit_side * ell**k


def neC0(ell: int, M: int, R: int, cf: int) -> int:
    # NuTwoUnc.lean:33. Nat subtraction does not truncate on this domain.
    assert ell >= 2 and M >= 1 and R >= 1 and cf >= 10
    return neA_prime(ell, M, R) + cf * (ell * M) - (ell * M + 1)


def main() -> None:
    ell = 2
    checks = 0
    # identity grid: the coordinate formulas, not class-cube membership
    for M in range(1, 5):
        for R in (1, 10, 21):
            for cf in (10, 12, 16):
                unit = neNu(M, R, cf)
                fine = neN(ell, M, R, cf)
                assert fine == unit * ell**2
                assert fine_side(ell, 2, unit) == fine
                lower = neC0(ell, M, R, cf)
                upper = lower + 1
                a_prime = neA_prime(ell, M, R)
                y1 = ell * M
                assert upper == a_prime + (cf - 1) * y1
                b_prime = neB_prime(ell, M, R, cf)
                assert b_prime - a_prime == (cf - 1) * ell * y1
                assert a_prime <= lower < upper < b_prime
                assert upper < fine
                checks += 1

    # smallest positive parameters with cf >= 10 (not a theorem witness)
    formula_min = {
        "ell": 2,
        "M": 1,
        "R": 1,
        "cf": 10,
        "unit_side": neNu(1, 1, 10),
        "fine_side": neN(2, 1, 1, 10),
    }
    # failEllCS_two smallest: m = 2 so M = 2^2, R = 1, c = 10 (NuA1.lean:44-53)
    fail_ell = {
        "ell": 2,
        "m": 2,
        "M": 4,
        "R": 1,
        "cf": 10,
        "unit_side": neNu(4, 1, 10),
        "fine_side": neN(2, 4, 1, 10),
    }
    # constFam_witness_two chooses R >= c (NuA3.lean:99-105)
    witness = {
        "ell": 2,
        "m": 2,
        "M": 4,
        "R": 10,
        "cf": 10,
        "unit_side": neNu(4, 10, 10),
        "fine_side": neN(2, 4, 10, 10),
    }
    cap = 8
    print(f"identity_checks {checks}")
    for name, row in (
        ("formula_min_cf10", formula_min),
        ("failEllCS_two_smallest", fail_ell),
        ("ConstFamWitnessTwo_R_ge_c", witness),
    ):
        print(
            f"{name} unit_side={row['unit_side']} fine_side={row['fine_side']} "
            f"exceeds_side_cap={row['fine_side'] > cap and row['unit_side'] > cap}"
        )
    print("operator_modelled no")
    print("reason witness fine side exceeds 8; genForm and Ginv were not evaluated")


if __name__ == "__main__":
    main()
