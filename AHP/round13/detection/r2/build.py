#!/usr/bin/env python3
"""Verbatim compact joins; writes only detection/r2. --publish adds shared R2 sources."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
SH=ROOT/'AHP/round13/shared/detection'
checks=[]
def fragment(file,start=None,end=None,after=None):
    data=(ROOT/file).read_text()
    lo=0 if start is None else data.index(start)
    hi=len(data) if end is None else data.index(end,lo if after is None else data.index(after,lo))
    piece=data[lo:hi]
    checks.append({'source':file,'start':lo,'end':hi,
        'sha256':hashlib.sha256(piece.encode()).hexdigest()})
    return piece
area=fragment('AHP/round13/detection/r2/Area.lean','/-!')
color=fragment('AHP/round13/detection/r1/ColorTrace.lean')
body=(OUT/'ColorAreaAppendix.lean.txt').read_text()
(OUT/'ColorArea.lean').write_text(color+'\n'+area+'\n'+body)
jet=fragment('AHP/round13/detection/r1/JetBridge.lean')
flip=fragment('AHP/round13/detection/r1/ColorTrace.lean',
    'namespace AdalyFormal.Round9.Guarded.QualitativeR2',
    'namespace AdalyFormal.Round10.Dictionary.Source')
selection=fragment('AHP/round13/detection/r1/ColorTrace.lean',
    '/-! Exact global-color selection rules',
    'namespace AdalyFormal.Round13.Detection.ColorTrace')
line=fragment('AHP/round12/kernel/r2/ActualResponse.lean',
    'namespace AdalyFormal.Round9.Guarded.Qualitative\nopen scoped RealInnerProductSpace Topology',
    'namespace AdalyFormal.Round9.Guarded.QualitativeR2\n',
    after='end AdalyFormal.Round10.Assembly.R2')
add=fragment('AHP/round12/shared/kernel/R1_ActualKernel.lean',
    'theorem uθ_add', '/-- The only coordinate identity')
add='namespace AdalyFormal.Round12.Kernel.Actual\n'+add+'end AdalyFormal.Round12.Kernel.Actual\n'
physical=(OUT/'PhysicalAreaAppendix.lean.txt').read_text()
(OUT/'PhysicalArea.lean').write_text(jet+'\n'+flip+selection+'\n'+area+'\n'+body+'\n'+line+'\n'+add+'\n'+physical)
(OUT/'COPIES.json').write_text(json.dumps(checks,indent=2)+'\n')
if '--publish' in sys.argv:
    SH.mkdir(exist_ok=True,parents=True)
    for name in ['Area','ColorArea','PhysicalArea']:
        (SH/f'R2_{name}.lean').write_bytes((OUT/f'{name}.lean').read_bytes())
