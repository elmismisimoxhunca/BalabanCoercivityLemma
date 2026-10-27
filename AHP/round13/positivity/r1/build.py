#!/usr/bin/env python3
"""Build compact certificates from verbatim round-12 components."""
from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parents[4]
work = root / 'AHP/round13/positivity/r1'
pieces = []
manifest = []
for rel, skip in [('AHP/round12/shared/noncancel/R2_FullPlaquette.lean', 0),
                  ('AHP/round12/shared/noncancel/R2_Mass.lean', 7),
                  ('AHP/round12/shared/noncancel/R2_Boundary.lean', 7)]:
    lines = (root / rel).read_text().splitlines(keepends=True)
    text = ''.join(lines[skip:])
    pieces.append(text)
    manifest.append({'source': rel, 'firstLine': skip+1, 'lastLine': len(lines),
                     'sha256': hashlib.sha256(text.encode()).hexdigest()})
text = '\n'.join(pieces) + (work / 'AbsorptionAppendix.lean.txt').read_text() + (work / 'PhysicalAppendix.lean.txt').read_text()
(work / 'MassAbsorption.lean').write_text(text)
(work / 'COPIES.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(f'MassAbsorption.lean: {len(text.splitlines())} lines')
family = (root / 'AHP/round12/shared/noncancel/R2_RightFamily.lean').read_text()
mass = ''.join((root / 'AHP/round12/shared/noncancel/R2_Mass.lean').read_text().splitlines(keepends=True)[7:])
leaves = family + '\n' + mass + (work / 'LeavesAppendix.lean.txt').read_text()
(work / 'EightLeaves.lean').write_text(leaves)
print(f'EightLeaves.lean: {len(leaves.splitlines())} lines')
# Reuse the freshly compiled compact flat positivity proof from the sibling track.
flat = ''.join((root / 'AHP/round13/shared/detection/R1_FlatUnit.lean').read_text().splitlines(keepends=True)[:1096])
fl = family.splitlines(keepends=True)
def span(a, b):
    return ''.join(fl[a-1:b])
local = flat + '\n' + span(8,222) + '\n' + span(433,444) + span(530,543) + '\n' + span(545,588) + '\n' + span(590,610).replace('open AdalyFormal.Round9.Guarded.Qualitative\n', '') + '\nend AdalyFormal.Round12.Noncancel.RightFamily\n'
local += (work / 'LocalPositiveAppendix.lean.txt').read_text()
(work / 'LocalPositive.lean').write_text(local)
print(f'LocalPositive.lean: {len(local.splitlines())} lines')
# Complete provenance, including the independent flat-positivity handoff.
extra = [
    {'target':'EightLeaves.lean','source':'AHP/round12/shared/noncancel/R2_RightFamily.lean','firstLine':1,'lastLine':693},
    {'target':'EightLeaves.lean','source':'AHP/round12/shared/noncancel/R2_Mass.lean','firstLine':8,'lastLine':91},
    {'target':'LocalPositive.lean','source':'AHP/round13/shared/detection/R1_FlatUnit.lean','firstLine':1,'lastLine':1096},
]
for a,b in [(8,222),(433,444),(530,543),(545,588),(590,610)]:
    extra.append({'target':'LocalPositive.lean','source':'AHP/round12/shared/noncancel/R2_RightFamily.lean','firstLine':a,'lastLine':b})
for row in manifest:
    row['target'] = 'MassAbsorption.lean'
for row in extra:
    chunk = ''.join((root/row['source']).read_text().splitlines(keepends=True)[row['firstLine']-1:row['lastLine']])
    if row['target']=='LocalPositive.lean' and row['firstLine']==590:
        row['removedUnusedOpen'] = 'open AdalyFormal.Round9.Guarded.Qualitative\n'
        chunk = chunk.replace(row['removedUnusedOpen'],'')
    row['sha256'] = hashlib.sha256(chunk.encode()).hexdigest()
    manifest.append(row)
(work / 'COPIES.json').write_text(json.dumps(manifest,indent=2)+'\n')
