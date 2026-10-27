#!/usr/bin/env python3
"""Compact verbatim round-12 spine, plus explicit conditional quantifier glue."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
records=[]
def part(path, a, b):
    p=ROOT/path; lines=p.read_text().splitlines(keepends=True)
    text=''.join(lines[a-1:b])
    records.append(dict(path=path,start_line=a,end_line=b,sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
response='AHP/round12/shared/kernel/R2_ResponseLine.lean'
crossing='AHP/round12/shared/kernel/R2_FirstCrossing.lean'
family='AHP/round12/shared/noncancel/R2_RightFamily.lean'
gauge='AHP/round12/shared/noncancel/R1_Star.lean'
text=part(response,1,2107)+'\n'
# Size identities are needed by the actual one-color witness below.
text+=part(family,284,297)+part(family,309,317)+'end AdalyFormal.Round4.Guarded.RefuteR1\n'
# Only the covariance lemma missing from the response harness.
text+=part(crossing,244,257)+part(crossing,357,398)+'end AdalyFormal.Round10.Dictionary\n'
# Generic whole-kernel trace argument and actual/canonical crossing application.
text+=part(crossing,1351,1553)+'\n'+part(crossing,1608,2060)+'\n'
# Valid RIGHT family. Shared definitions above are not re-declared.
text+=part(family,8,12)+part(family,19,222)+'\n'
text+=part(family,415,693)+'\n'
# The right-star quarter gauge, with its only local group helper.
text+=part(gauge,586,600)+part(gauge,643,659)+'\nend AdalyFormal.Round12.Noncancel.Gauge\n'
text+=(HERE/'SpineAppendix.lean.txt').read_text()
(HERE/'Spine.lean').write_text(text)
(HERE/'SPINE_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('Spine.lean:',len(text.splitlines()),'lines')
