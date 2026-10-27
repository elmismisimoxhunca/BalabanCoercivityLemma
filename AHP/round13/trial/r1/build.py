"""Build the compact P1 source, copying frozen round-12 interfaces verbatim.
This script does not compile or alter any earlier round. Compilation must use lean1.sh.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--publish', action='store_true')
args = parser.parse_args()
chunks = []
copies = []

def copy_fragment(relative, fragment=None, omit_import=False):
    source = ROOT / relative
    original = source.read_text()
    body = original if fragment is None else fragment
    if omit_import:
        body = body.removeprefix('import DrEquiv\n')
    assert body in original
    start = original.index(body)
    copies.append({
        'source': relative,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'source_first_line': original[:start].count('\n') + 1,
        'source_last_line': original[:start+len(body)].count('\n'),
        'fragment_sha256': hashlib.sha256(body.encode()).hexdigest(),
        'fragment_bytes': len(body.encode()),
        'destination_first_line': ''.join(chunks).count('\n') + 1,
    })
    chunks.append(body + '\n')

copy_fragment('AHP/round12/shared/noncancel/R2_RightFamily.lean')
copy_fragment('AHP/round12/shared/noncancel/R2_Boundary.lean', omit_import=True)
copy_fragment('AHP/round12/shared/noncancel/R2_Mass.lean', omit_import=True)
algebra = 'AHP/round12/shared/noncancel/R2_StarLocal.lean'
prefix = (ROOT / algebra).read_text().split('/-! Full three-color identities:')[0]
copy_fragment(algebra, prefix, omit_import=True)
crossing_path = 'AHP/round12/shared/kernel/R2_FirstCrossing.lean'
crossing = (ROOT / crossing_path).read_text()
ns = 'AdalyFormal.Round9.Guarded.AnalyticR1'
twist = 'namespace ' + ns + '\n' + crossing.split('namespace ' + ns + '\n',1)[1].split('end ' + ns,1)[0] + 'end ' + ns
copy_fragment(crossing_path, twist)

own = []
for name in ['TrialBody', 'CollarBody', 'PlaquetteBody', 'EvalBody', 'EnergyBody']:
    body = (OUT / (name + '.lean.txt')).read_text()
    chunks.append(body + '\n')
    own.extend(re.findall(r'^(?:abbrev|def|theorem) (\w+)', body, re.M))
# Print every new declaration outside the namespace so Classical.choice is fully qualified.
chunks.append('\n'.join('#print axioms AdalyFormal.Round13.Trial.' + name for name in own) + '\n')
text = ''.join(chunks)
(OUT / 'Trial.lean').write_text(text)
(OUT / 'COPIES.json').write_text(json.dumps(copies, indent=2) + '\n')
if args.publish:
    dest = ROOT / 'AHP/round13/shared/trial/R1_Trial.lean'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(text)
print(f'Wrote {len(text.splitlines())} lines, {len(own)} new declarations; {len(copies)} verbatim source fragments.')
