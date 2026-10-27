#!/usr/bin/env python3
"""Assemble compact R4 hull criterion. Never compile the historical Attempt here."""
from pathlib import Path
import json, hashlib
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def put(path, data):
    if isinstance(data, str): data = data.encode()
    if not path.exists() or path.read_bytes() != data: path.write_bytes(data)
cone = (HERE/'Cone.lean').read_bytes().replace(b'import D1IVT\n', b'', 1)
base = ROOT/'AHP/round10/shared/assembly/R3_EnergyGlue.lean'
appendix = (HERE/'ConeActualAppendix.lean').read_bytes()
cofinal = (HERE/'CofinalAppendix.lean').read_bytes()
put(HERE/'Compact.lean', base.read_bytes()+b'\n'+cone+b'\n'+appendix+b'\n'+cofinal)
# Exact unchanged historical R9 bytes, via the already assembled R3 prefix.
r9 = ROOT/'AHP/round9/qualitative-r2/Attempt.lean'
r3 = ROOT/'AHP/round10/assembly/r3/Attempt.lean'
assert r3.read_bytes().startswith(r9.read_bytes())
parts = [r3.read_bytes(), cone, appendix]
for name in ['CofinalAppendix.lean', 'GoalAppendix.lean']:
    if (HERE/name).exists(): parts.append((HERE/name).read_bytes())
# Include the independently compiled R4 cross-track bodies unchanged, omitting
# only definitions already present in the exact historical prefix.
dictionary = ROOT/'AHP/round10/shared/dictionary/R4_ColorResponse.lean'
ds = dictionary.read_bytes()
# The two dictionary sections start after copied flip definitions and precede
# copied side-length geometry; use precise namespace boundaries instead.
ci = ds.index(b'namespace AdalyFormal.Round10.Dictionary.Color\n')
gi = ds.index(b'namespace AdalyFormal.Round4.Guarded.RefuteR1\n', ci)
oi = ds.index(b'namespace AdalyFormal.Round10.Dictionary.ColorObstruction\n', gi)
parts += [b'noncomputable section\n'+ds[ci:gi], b'noncomputable section\n'+ds[oi:]]
poly = ROOT/'AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean'
parts.append(poly.read_bytes().replace(b'import D1IVT\n', b'', 1))
put(HERE/'Attempt.lean', b'\n'.join(parts))
published = ROOT/'AHP/round10/shared/assembly/R4_ResponseHull.lean'
put(published, (HERE/'Compact.lean').read_bytes())
put(HERE/'ASSEMBLY.json', json.dumps({
    'r9_sha256':hashlib.sha256(r9.read_bytes()).hexdigest(),
    'r9_bytes':r9.stat().st_size,
    'r9_prefix_exact':(HERE/'Attempt.lean').read_bytes().startswith(r9.read_bytes()),
    'historical_compiled':False,
    'compact_prefix':str(base.relative_to(ROOT)),
    'compact_prefix_exact':(HERE/'Compact.lean').read_bytes().startswith(base.read_bytes()),
}, indent=2)+'\n')
print('Compact:', len((HERE/'Compact.lean').read_text().splitlines()), 'lines')
print('Historical Attempt: assembled only, NOT COMPILED')
