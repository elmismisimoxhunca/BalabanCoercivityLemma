#!/usr/bin/env python3
"""Term-by-term structure of c1 = 2 sum_j h_j C2_j(W0 v0) for the left-twist vacuum mode
(q = 1 geometry with Bloch phase k on the diagonal).  Prints, per coarse direction-1 bond
x = p + 2j of Omega_1, the source h_j, the jet C2_j and the share of c1, and the mode's
transverse-field amplitude ratio across the collar (decay rate check).  Evidence only."""
import sys
sys.dont_write_bytecode = True
from lefttwist import *   # noqa: F401,F403


def run(R, k, dps):
    mp.mp.dps = dps
    f = LeftFamily(1, R, mp.mpf(0), 0, 0, 1)
    f.ph = (mp.exp(2j * k), mp.exp(2j * k))
    f.assemble()
    S = f.boundary_inverse()
    t0m, t1m, t2m = f.theta(0), f.theta(mp.pi / 2), f.theta(mp.pi)
    Cm, Am = (t0m + t2m) / 2, (t0m - t2m) / 2
    Bm = t1m - Cm

    def low(t):
        return mp.eighe(S + Cm + mp.cos(t) * Am + mp.sin(t) * Bm, eigvals_only=True)[0]
    t = mp.findroot(low, (mp.mpf('0.45'), mp.mpf('0.62')), solver='secant',
                    tol=mp.power(10, -dps + 15), verify=False)
    ev, V = mp.eighe(S + Cm + mp.cos(t) * Am + mp.sin(t) * Bm)
    rhs = S * V[:, 0]
    x = [sum(f.X[j][i] * rhs[j] for j in range(len(f.X))) for i in range(f.aug.n)]
    norm = mp.sqrt(sum(abs(z)**2 for z in x[:f.n]))
    x = [z / norm for z in x]
    w = f.dressed(x[:f.n], x[f.n:f.n + f.H.n])
    h = leading_h(f)
    c1, terms = f.correction(w, h)
    T = 4 * (1 - mp.cos(k))
    rho = (3 + T - mp.sqrt((3 + T)**2 - 4)) / 2
    print('k', mp.nstr(k, 8), 'root', mp.nstr(t, 15), 'c1', mp.nstr(c1, 12),
          'K_L', mp.nstr(c1 / rho**(4 * R), 12), 'rho', mp.nstr(rho, 12))
    rows = []
    for idx, (b, hb, tb) in enumerate(zip(f.b1, h, terms)):
        if hb:
            jx = (b[0][0] - f.p) // 2
            rows.append((jx, b[1], hb, tb))
    for jx, d, hb, tb in rows[:8]:
        print(f'  j={jx:3d} dir={d} h={mp.nstr(hb, 10):>16} term={mp.nstr(tb, 10):>18} share={mp.nstr(tb / c1, 8)}')
    # collar decay of the dominant field component along x (cell site (0,0))
    ratios = []
    for xx in range(f.lo + 2, f.p - 2):
        vals = [abs(x[f.em[f.bi[((xx, 0, 0), mu)]]]) for mu in range(3)]
        nxt = [abs(x[f.em[f.bi[((xx + 1, 0, 0), mu)]]]) for mu in range(3)]
        mu = max(range(3), key=lambda m: vals[m])
        ratios.append(nxt[mu] / vals[mu])
    print('  collar successive ratios of the dominant component:', [mp.nstr(r, 10) for r in ratios])
    return dict(k=k, root=t, c1=c1, K_L=c1 / rho**(4 * R), rho=rho,
                terms=[dict(j=jx, dir=d, h=hb, term=tb, share=tb / c1) for jx, d, hb, tb in rows])


if __name__ == '__main__':
    out = []
    for ks in ['-pi/8', '-0.267', '-pi/32']:
        mp.mp.dps = 50
        k = mp.mpf(eval(ks.replace('pi', 'mp.pi')))
        out.append(run(8, k, 50))
    (OUTDIR / 'terms_left_R8_p50.json').write_text(json.dumps(jsonable(out), indent=2) + '\n')
