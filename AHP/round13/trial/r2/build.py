"""Retain the accepted R1 certificate verbatim and append only the R2 handoff."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
SHARED = ROOT / 'AHP/round13/shared/trial'
R1 = ROOT / 'AHP/round13/trial/r1/Trial.lean'
ACCEPTED_SHA = '65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b'

parser = argparse.ArgumentParser()
parser.add_argument('--publish', action='store_true')
args = parser.parse_args()
prefix = R1.read_bytes()
assert hashlib.sha256(prefix).hexdigest() == ACCEPTED_SHA
assert prefix == (SHARED / 'R1_Trial.lean').read_bytes()
assert prefix == R1.with_name('Trial.verify.lean').read_bytes()
body = (OUT / 'HandoffBody.lean.txt').read_bytes()
source = prefix + body
(OUT / 'Trial.lean').write_bytes(source)
(OUT / 'COPIES.json').write_text(json.dumps({
    'source': str(R1.relative_to(ROOT)),
    'source_sha256': ACCEPTED_SHA,
    'prefix_bytes': len(prefix),
    'prefix_lines': len(prefix.splitlines()),
    'appendix_sha256': hashlib.sha256(body).hexdigest(),
    'inherited_interface_manifest': 'AHP/round13/trial/r1/COPIES.json',
}, indent=2) + '\n')
if args.publish:
    SHARED.mkdir(parents=True, exist_ok=True)
    (SHARED / 'R2_Trial.lean').write_bytes(source)
    (SHARED / 'R2_HandoffBody.lean.txt').write_bytes(body)
print(f'Wrote {len(source.splitlines())} lines; R1 prefix unchanged; published={args.publish}')
