#!/usr/bin/env python3
"""Assemble only this round's compact proofs; never compile historical concatenations."""
from pathlib import Path

base = Path(__file__).resolve().parent
moving = (base / 'PolynomialGrid.lean').read_bytes() + (base / 'MovingRootPart.lean.txt').read_bytes()
(base / 'MovingRoot.lean').write_bytes(moving)
complete = moving + (base / 'SeedObstructionPart.lean.txt').read_bytes()
(base / 'SeedObstruction.lean').write_bytes(complete)
print('Assembled MovingRoot.lean and SeedObstruction.lean; compilation is separate.')
