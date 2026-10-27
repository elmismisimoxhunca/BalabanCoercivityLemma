#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
path='AHP/round10/shared/dictionary/R4_ColorSelection.lean'
text=(ROOT/path).read_text()
records=[dict(path=path,entireFile=True,sha256=hashlib.sha256(text.encode()).hexdigest())]
path2='AHP/round10/shared/dictionary/R4_ColorResponse.lean'
s=(ROOT/path2).read_text(); a=s.index('theorem half_pauliE1'); b=s.index('theorem oneColor_charged',a); helpers=s[a:b]
records.append(dict(path=path2,start='theorem half_pauliE1',end='theorem oneColor_charged',sha256=hashlib.sha256(helpers.encode()).hexdigest()))
text+='''\nnamespace AdalyFormal.Round10.Dictionary.ColorObstruction
open AdalyFormal.Balaban.CovariantOperators (RMap RMap_coe_apply)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt)
open AdalyFormal.Round10.Dictionary.Color
'''+helpers+'\nend AdalyFormal.Round10.Dictionary.ColorObstruction\n'
text+=(HERE/'ColorTraceAppendix.lean.txt').read_text()
(HERE/'ColorTrace.lean').write_text(text)
(HERE/'COLOR_TRACE_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('wrote',len(text.splitlines()),'lines')
