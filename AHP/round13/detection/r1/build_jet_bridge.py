#!/usr/bin/env python3
"""Compact join: existing physical top-jet dictionary + proved flat full N unit."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
records=[]
def section(path,start,end=None):
    source=(ROOT/path).read_text(); a=source.index(start)
    b=source.index(end,a) if end is not None else len(source)
    text=source[a:b]
    records.append(dict(path=path,start=start,end=end,sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
jet='AHP/round10/shared/dictionary/R3_JetDetection.lean'
flat='AHP/round13/detection/r1/FlatUnit.lean'
text=section(jet,'import DrEquiv')
text+=section(flat,'namespace AdalyFormal.Round3.Guarded.RefuteR2',
    'namespace AdalyFormal.Round9.Guarded.AnalyticR2\nopen scoped RealInnerProductSpace Topology\nopen AdalyFormal.Target.ClayStatement\nopen AdalyFormal.StatementLane\nopen AdalyFormal.StatementLaneG\nopen AdalyFormal.IngredientFamilyR2\nopen AdalyFormal.Round2.Guarded.Pin\nopen AdalyFormal.Round4.Guarded.RefuteR1\nopen AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)\nopen AdalyFormal.Balaban.QjComposite (stepAverage)\nopen AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)\nnoncomputable abbrev flatData')
text+=section(flat,'namespace AdalyFormal.Round13.Detection\n')
text+=(HERE/'JetBridgeAppendix.lean.txt').read_text()
(HERE/'JetBridge.lean').write_text(text)
(HERE/'JET_BRIDGE_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('wrote',len(text.splitlines()),'lines')
