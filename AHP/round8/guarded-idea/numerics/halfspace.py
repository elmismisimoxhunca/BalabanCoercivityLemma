#!/usr/bin/env python3
"""Half-space crossing angle t_inf(k) for diagonal transverse momentum (k,k),
from the closed boundary equation recorded in AHP/round6/probe/PROBE.md sec. 4:
 (1+T cos t+4 sin k sin t)((2+T-rho_k)/(1+T)+cos t) - 4(1-cos(2t+k)) = 0,
 T = 4(1-cos k), rho_k = (3+T-sqrt((3+T)^2-4))/2.
Checks k=0 and k=-pi/8 against the probe's finite-volume roots, then lists the
allowed momenta of the q-dilated torus (fine wave number 2 pi j/(8q))."""
import mpmath as mp
mp.mp.dps = 30
def F(t, k):
    T = 4*(1-mp.cos(k)); rho = (3+T-mp.sqrt((3+T)**2-4))/2
    return (1+T*mp.cos(t)+4*mp.sin(k)*mp.sin(t))*((2+T-rho)/(1+T)+mp.cos(t)) - 4*(1-mp.cos(2*t+k))
def troot(k):
    # first sign change on (0, pi/2)
    ts = [mp.mpf(i)/400*mp.pi/2 for i in range(1, 401)]
    prev = F(ts[0], k)
    for a, b in zip(ts, ts[1:]):
        fb = F(b, k)
        if prev > 0 and fb <= 0:
            return mp.findroot(lambda t: F(t, k), (a, b), solver='bisect')
        prev = fb
    return None
print('k=0      ', troot(mp.mpf(0)), ' probe q=1 root 0.5865589686386088')
print('k=-pi/8  ', troot(-mp.pi/8), ' probe q=2 (7,7) root 0.5639715179855609')
best = min(((troot(-mp.pi*j/400), j) for j in range(0, 401) if troot(-mp.pi*j/400) is not None))
print('continuum minimum over diagonal k in [-pi,0]: t=', best[0], ' k=-pi*', best[1], '/400')
for q in [1, 2, 4, 8]:
    rows = []
    for j in range(0, 8*q):
        k = 2*mp.pi*j/(8*q)
        if k > mp.pi: k -= 2*mp.pi
        r = troot(k)
        if r is not None: rows.append((r, j, k))
    rows.sort()
    r, j, k = rows[0]
    iy = (4*q*2*k/(2*mp.pi)) % (4*q)
    print(f'q={q}: best diagonal fine momentum j={j} (k={mp.nstr(k,8)}), t_inf={mp.nstr(r,15)}, character iy=iz={mp.nstr(iy,6)}; next', [(mp.nstr(a,10), b) for a, b, _ in rows[1:4]])
