#!/usr/bin/env python3
"""Integrate the freshly compiled P1 theorem without re-declaring shared interfaces."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[4]; HERE=Path(__file__).resolve().parent
p=ROOT/'AHP/round13/shared/trial/R1_Trial.lean'; lines=p.read_text().splitlines(keepends=True)
records=[]
def part(a,b):
    text=''.join(lines[a-1:b]); records.append(dict(path=str(p.relative_to(ROOT)),start_line=a,end_line=b,sha256=hashlib.sha256(text.encode()).hexdigest())); return text
text=(HERE/'StartedSpine.lean').read_text()+'\n'
# Boundary, Mass, Star/Plaquette algebra; RightFamily and TwistSpace already exist.
text+=part(695,1225)+'\n'+part(1246,len(lines))+'\n'
text+=(HERE/'P1Appendix.lean.txt').read_text()
(HERE/'P1Spine.lean').write_text(text)
(HERE/'P1_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('P1Spine.lean:',len(text.splitlines()),'lines')
