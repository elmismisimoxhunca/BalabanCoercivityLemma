#!/usr/bin/env python3
"""Verbatim compact reconstruction of the historical full flat constraint unit."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
records = []
def part(path, first, last):
    source = (ROOT/path).read_text()
    a = source.index(first)
    b = source.index(last, a)
    text = source[a:b]
    records.append(dict(path=path, start=first, end=last, startLine=source[:a].count('\n')+1, sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
response = 'AHP/round12/shared/kernel/R2_ResponseLine.lean'
family = 'AHP/round12/shared/noncancel/R2_RightFamily.lean'
analytic = 'AHP/round9/analytic-r2/Attempt.lean'
text = part(response, 'import DrEquiv', 'namespace AdalyFormal.Round4.Guarded.RefuteR1')
text += 'noncomputable section\n'
text += part(family, 'namespace AdalyFormal.Round4.Guarded.RefuteR1\n', 'namespace AdalyFormal.Round5.Guarded.IVTR1')
text += part(family, 'namespace AdalyFormal.Round3.Guarded.RefuteR2\n', 'theorem dil_shift_zero')
text += '\nend AdalyFormal.Round4.Guarded.RefuteR1\n'
opens = '''open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
'''
text += '\nnamespace AdalyFormal.Round9.Guarded.AnalyticR2\n' + opens
text += 'variable {L : PeriodicLatticeExtent}\n'
text += part(analytic, "theorem Qcomposite_one'", 'theorem cont_Qlev')
text += part(analytic, 'theorem QfullOf_apply', 'theorem C2fullOf_apply')
text += part(analytic, 'theorem dil_G_k', 'theorem dil_out_site')
text += part(analytic, 'theorem delW_zero', 'end DilUnits')
text += '\nend AdalyFormal.Round9.Guarded.AnalyticR2\n'
text += part(analytic, 'namespace AdalyFormal.Round9.Guarded.AnalyticR2\n\nopen scoped RealInnerProductSpace Topology\nopen Filter Set\n\n/-! ## J.', 'namespace AdalyFormal.Round9.Guarded.AnalyticR2\n\nopen scoped RealInnerProductSpace Topology\nopen Filter Set\n\nsection Final')
text += '\nnamespace AdalyFormal.Round9.Guarded.AnalyticR2\n' + opens
text += part(response, 'noncomputable abbrev flatData', 'noncomputable def vacCoupling')
text += '\nend AdalyFormal.Round9.Guarded.AnalyticR2\n'
text += part(response, 'namespace AdalyFormal.Round10.Dictionary.KKT\n', 'omit [FiniteDimensional ℝ E]')
text += '\nend AdalyFormal.Round10.Dictionary.KKT\n'
text += (HERE/'FlatUnitAppendix.lean.txt').read_text()
(HERE/'FlatUnit.lean').write_text(text)
(HERE/'FLAT_UNIT_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('wrote',len(text.splitlines()),'lines')
