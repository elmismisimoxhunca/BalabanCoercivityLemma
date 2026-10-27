#!/usr/bin/env python3
"""Copy compact operative declarations verbatim; write only this round directory."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
records=[]
def section(path,start,end):
    full=(ROOT/path).read_text()
    a=full.index(start);b=full.index(end,a)
    t=full[a:b]
    records.append({'path':path,'start':start,'end':end,'start_line':full[:a].count('\n')+1,
      'end_line_exclusive':full[:b].count('\n')+1,'sha256':hashlib.sha256(t.encode()).hexdigest()})
    return t
common='''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
'''
r9='AHP/round9/qualitative-r2/Attempt.lean'
r1='AHP/round12/noncancel/r1/Attempt.lean'
kern='AHP/round12/kernel/r1/ActualKernel.lean'
text='''import DrEquiv
/-! A concrete cofinal family of valid right-exterior-star paths.
No kernel-line or response-detection conclusion is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
'''
text+=section(r1,'namespace AdalyFormal.Round9.Guarded.QualitativeR2\n','namespace AdalyFormal.Round12.Noncancel.Gauge\n')
text+=section(kern,'namespace AdalyFormal.Round2.Guarded.Pin\n','namespace AdalyFormal.Round9.Guarded.QualitativeR2\n')
text+='\nnamespace AdalyFormal.Round3.Guarded.RefuteR2\n'+common
text+=section(r9,'theorem zero_coord_le_pdist','/-- All six frozen admissibility clauses')
text+='\nend AdalyFormal.Round3.Guarded.RefuteR2\n'
text+='\nnamespace AdalyFormal.Round4.Guarded.RefuteR1\n'+common+'''open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
'''
text+=section(r9,'theorem dil_fine_bound','theorem dil_torus')
text+=section(r9,'theorem dil_admissible','def dilEmb')
text+=section(r9,'theorem dil_shift_zero','theorem dil_coverage')
text+='\n#print axioms dil_admissible\nend AdalyFormal.Round4.Guarded.RefuteR1\n'
text+='\nnamespace AdalyFormal.Round5.Guarded.IVTR2\n'+common+'''open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
'''
text+=section(r9,'def rightSite','theorem twist_eq_Uth_off_defect')
text+='\n#print axioms rightSite_bd\nend AdalyFormal.Round5.Guarded.IVTR2\n'
text+='\n'+(HERE/'RightFamilyAppendix.lean.txt').read_text()
(HERE/'RightFamily.lean').write_text(text)
(HERE/'FAMILY_COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('Wrote compact RightFamily.lean:',len(text.splitlines()),'lines')
