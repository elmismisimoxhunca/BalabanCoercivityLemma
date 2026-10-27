#!/usr/bin/env python3
"""Build only compact harnesses in dictionary/r3; earlier rounds remain read-only."""
from pathlib import Path
import re, json, hashlib
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'AHP/round10/dictionary/r3'
P=ROOT/'AHP/round10/dictionary/r2/PhaseSource.lean'
s=P.read_text()
records=[]
def save(path, content):
    if not path.exists() or path.read_text()!=content:
        path.write_text(content)
def fragment(path, start, end):
    text=path.read_text(); a=text.index(start); b=text.index(end,a)
    frag=text[a:b].rstrip()+'\n'
    records.append({'source':str(path.relative_to(ROOT)), 'start':text[:a].count('\n')+1,
        'sha256':hashlib.sha256(frag.encode()).hexdigest(), 'fragment':frag})
    return frag
header='''import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.PhaseSource
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}
'''
base=header+fragment(P,'def circulation','theorem holonomy_phase')
base+=fragment(P,'def oriented','def sourceScalar')
base+=fragment(P,'def linearSourceScalar','theorem FnuMuLoc_phase')
base+=fragment(P,'def sourceLinear','theorem sourceField_hasDerivAt')
base+='end AdalyFormal.Round10.Dictionary.PhaseSource\n'
save(OUT/'Scalar.lean',base+'\n'+(OUT/'ScalarAppendix.lean').read_text())
if (OUT/'ActualAppendix.lean').exists():
    source=ROOT/'AHP/round10/dictionary/r2/Source.lean'
    prefix=source.read_text()
    records.append({'source':str(source.relative_to(ROOT)), 'start':1,
        'sha256':hashlib.sha256(prefix.encode()).hexdigest(), 'wholeFile':True})
    save(OUT/'Actual.lean',prefix+'\n'+(OUT/'ScalarAppendix.lean').read_text()+'\n'+
        (OUT/'ActualAppendix.lean').read_text())
if (OUT/'JetAppendix.lean').exists():
    nv=ROOT/'AHP/round10/shared/nonvanishing/R3_DilatedFlux.lean'
    body=nv.read_text()
    geometry_start=body.index('namespace AdalyFormal.Round4.Guarded.RefuteR1')
    geom_defs_start=body.index('def dilLu',geometry_start)
    geom_defs_end=body.index('theorem dil_unit_size',geom_defs_start)
    geom_body=body[geom_defs_start:geom_defs_end]
    body=body[:geom_defs_start]+body[geom_defs_end:]
    body='\n'.join(l for l in body.splitlines() if not l.startswith('import '))+'\n'
    # Preserve every retained source body; only the two duplicate geometry defs are omitted.
    records.append({'source':str(nv.relative_to(ROOT)), 'sha256':hashlib.sha256(nv.read_bytes()).hexdigest(),
        'wholeFileExceptImportsAndDuplicateGeometry':True, 'omitted':geom_body})
    actual=(OUT/'Actual.lean').read_text()
    combined=actual.replace('import DrEquiv\n','import DrEquiv\nimport ZXR2Flat6\n',1)
    save(OUT/'JetDetection.lean',combined+'\n'+body+'\n'+(OUT/'JetAppendix.lean').read_text())
save(OUT/'COPIES.json',json.dumps(records,indent=2)+'\n')
