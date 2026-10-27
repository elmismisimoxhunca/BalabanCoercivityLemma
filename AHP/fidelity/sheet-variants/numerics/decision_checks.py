#!/usr/bin/env python3
"""Decision diagnostics; evidence only, not proof.
Sources: lean/src/ZStatementP428.lean:42-43 (scaleUp), :51 (bigSide),
:58-67 (pcd/pdist), :73-83 (tower divisibility), :189-195 (LambdaOK),
:286-289 (TorusOK, on UNIT extent Lu, not fine extent scaleUp ell k Lu).
No analytic operators. Every fine/unit side used is <= 8.
"""
from itertools import product


def pdist(n, x, y):
    # lean/src/ZStatementP428.lean:58-67
    return sum(min(abs(a-b), n-abs(a-b)) for a, b in zip(x, y))


fits = []
for ell in range(2, 9):
    for m in range(1, 4):
        M = ell**m
        for k in range(2, 4):
            for unit in range(1, 9):
                fine = unit * ell**k  # scaleUp stores fine-1
                if fine > 8:
                    continue
                torus_ok = unit % ell == 0 and ell < unit and unit % M == 0
                divides = all(fine % (M * ell**j) == 0 for j in range(k+1))
                if torus_ok and divides:
                    fits.append((ell, M, k, unit, fine))
assert fits == []
print('actual headline k>=2, fine side<=8: fits =', fits)
print('attack candidate (ell,M,k,fine)=(2,2,2,8) has unit side=2, violating ell<unit')

unit, ell, k = 4, 2, 1
fine = unit * ell**k
points = list(product(range(unit), repeat=3))
for R, M in ((3, 2), (1, 1)):
    true_pairs = false_pairs = mismatches = 0
    for y, z in product(points, repeat=2):
        ey, ez = tuple(ell**k*a for a in y), tuple(ell**k*a for a in z)
        du, df = pdist(unit, y, z), pdist(fine, ey, ez)
        u, f = R*M < du, R*M*ell**k < df
        true_pairs += u
        false_pairs += not u
        mismatches += df != ell**k*du or u != f
    assert mismatches == 0
    if (R, M) == (1, 1):
        assert true_pairs > 0 and false_pairs > 0
    print(f'R={R}, M={M}: true={true_pairs}, false={false_pairs}, mismatches={mismatches}')
print('all decision checks passed')
