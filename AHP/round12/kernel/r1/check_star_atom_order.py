#!/usr/bin/env python3
"""Local regression: physical-edge order versus frozen a1,a2,a3,a4 order.
Checks numerical transcription against the compiled three-atom formulas, not a
Lean identification of the global carrier or the reconstructed physical jets.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json
from star_crosscheck import mp, geometry, perturbation

mp.mp.dps = 100
out = Path(__file__).resolve().parent
checks = []
for side in ['left', 'right']:
    boundary = 4 if side == 'left' else 12 * 20 + 12
    plaquettes, bonds = geometry(boundary, side)
    center = bonds.index(((boundary - 1, 0, 0), 0))
    for t in [mp.mpf('0.371'), mp.mpf('1.207987856419019'), mp.pi / 2, mp.pi, -mp.mpf('0.371')]:
        for zero_center in [False, True]:
            v = mp.matrix([mp.mpc(mp.mpf(i + 1) / 7, mp.mpf(2 * i - 3) / 11)
                           for i in range(len(bonds))])
            if zero_center:
                v[center] = 0
            matrix_energy = mp.re((v.H * perturbation(t, 1, plaquettes, bonds, side) * v)[0])
            atom_energy = mp.mpf(0)
            zero_atoms = []
            for p in plaquettes:
                # Physical edge order: (x,mu), (x+mu,nu), (x+nu,mu), (x,nu).
                edge = [v[bonds.index(e)] if e in bonds else mp.mpc(0) for e in p]
                if side == 'left':
                    # Frozen atoms: -R(U(x,nu))*edge[2], -edge[3], edge[0], R(U(x,mu))*edge[1].
                    atoms = [-mp.exp(2j * t) * edge[2], -edge[3], edge[0], edge[1]]
                    assert atoms[1] == 0
                    triple = [atoms[0], atoms[2], atoms[3]]
                    s = -mp.sin(t)
                    zero_atoms.append(2)
                else:
                    atoms = [-edge[2], -edge[3], edge[0], edge[1]]
                    assert atoms[3] == 0
                    triple = atoms[:3]
                    s = mp.sin(t)
                    zero_atoms.append(4)
                x, y, z = triple
                atom_energy += (mp.cos(t) * abs(x + y + z)**2
                    + 2 * s * mp.im(mp.conj(x) * y + mp.conj(x) * z + mp.conj(y) * z))
            err = abs(matrix_energy - atom_energy)
            assert err < mp.mpf('1e-90'), (side, t, err)
            checks.append({'side': side, 'angle': mp.nstr(t, 20), 'central_zero': zero_center,
                           'zero_frozen_atoms': zero_atoms, 'absolute_error': mp.nstr(err, 12)})
result = {'pass': True, 'precision_digits': 100, 'checks': checks,
          'max_absolute_error': mp.nstr(max(mp.mpf(c['absolute_error']) for c in checks), 12),
          'mapping': 'Frozen a1,a2,a3,a4 correspond to physical zero-based edges 2,3,0,1 with transports/signs.',
          'qualification': 'Numerical local algebra regression only; not global frozen-operator identification.'}
(out / 'STAR_ATOM_ORDER.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
