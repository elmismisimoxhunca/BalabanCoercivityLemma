#!/usr/bin/env python3
"""Assemble the frozen round-9 byte prefix and this round's verified components.
Writes only assembly/r1/Attempt.lean. Run from any directory.
"""
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
prefix = (ROOT / 'AHP/round9/qualitative-r2/Attempt.lean').read_bytes()
parts = [HERE / 'snap/SourceDominance.lean', HERE / 'Cofinal.lean', HERE / 'Glue.lean']
result = bytearray(prefix)
for path in parts:
    data = path.read_bytes()
    if data.startswith(b'import D1IVT\n'):
        data = data[len(b'import D1IVT\n'):]
    result.extend(b'\n')
    result.extend(data)
(HERE / 'Attempt.lean').write_bytes(result)
assert bytes(result).startswith(prefix)
print('Assembled', HERE / 'Attempt.lean', 'with unchanged prefix bytes', len(prefix))
