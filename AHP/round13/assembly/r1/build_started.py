#!/usr/bin/env python3
"""Add the historical flat positive-start proof and frozen continuity specialization."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[4]; HERE=Path(__file__).resolve().parent
p=ROOT/'AHP/round9/qualitative-r2/Attempt.lean'
s=p.read_text().splitlines(keepends=True)
records=[]
def part(a,b):
    text=''.join(s[a-1:b]); records.append(dict(path=str(p.relative_to(ROOT)),start_line=a,end_line=b,sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
text='import DrPath3\n'+(HERE/'Spine.lean').read_text()+'\n'
text+='''namespace AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Round4.Guarded.RefuteR1
variable {L : PeriodicLatticeExtent}
'''+part(8914,8918)+part(9911,9911)+part(9466,9468)+'end AdalyFormal.Round9.Guarded.AnalyticR2\n'
text+=part(9960,10766)+'end FlatCarrier\nend AdalyFormal.Round9.Guarded.AnalyticR2\n'
text+='''namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
'''+part(5662,5698)+part(5723,5735)+'end AdalyFormal.Round9.Guarded.QualitativeR2\n'
text+=(HERE/'StartAppendix.lean.txt').read_text()
(HERE/'StartedSpine.lean').write_text(text)
(HERE/'START_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('StartedSpine.lean:',len(text.splitlines()),'lines')
