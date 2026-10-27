#!/usr/bin/env python3
"""Check the small neutral functional declaration after the published dictionary prefix."""
from pathlib import Path
import re,hashlib,json
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
p=REPO/'AHP/round10/shared/dictionary/R3_FreeSource.lean'
s=p.read_text()
s=s.replace('import DrEquiv\n','import DrEquiv\nimport ZXR2Flat6\n',1)
fragment=(ROOT/'DilatedAppendix.lean.txt').read_text()
a=fragment.index('noncomputable def neutralFunctional')
b=fragment.index('\n\n',a)
body=fragment[a:b]
reg=s+'''\nnamespace AdalyFormal.Round10.Nonvanishing.Regression
open scoped RealInnerProductSpace
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner (pauliE3)
'''+body+'''
#print axioms neutralFunctional
end AdalyFormal.Round10.Nonvanishing.Regression
'''
(ROOT/'AfterDictionary.lean').write_text(reg)
(ROOT/'REGRESSION.json').write_text(json.dumps({'dictionary':str(p.relative_to(REPO)),'dictionary_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'statement':'neutralFunctional with the literal source proof after the published dictionary prefix'},indent=2)+'\n')
