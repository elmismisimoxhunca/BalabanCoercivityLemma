#!/usr/bin/env python3
"""Compact assembly only. Copies immutable earlier declarations verbatim."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
records=[]
def section(path,start,end):
    full=(ROOT/path).read_text()
    a=full.index(start);b=full.index(end,a)
    text=full[a:b]
    records.append({'path':path,'start_line':full[:a].count('\n')+1,
      'end_line_exclusive':full[:b].count('\n')+1,
      'sha256':hashlib.sha256(text.encode()).hexdigest()})
    return text
prefix=(ROOT/'AHP/round10/shared/dictionary/R1_Dictionary.lean').read_text()
records.append({'path':'AHP/round10/shared/dictionary/R1_Dictionary.lean',
    'sha256':hashlib.sha256(prefix.encode()).hexdigest(),'entire_file':True})
source='AHP/round10/shared/assembly/R2_SourceGlue.lean'
psd=section(source,'namespace AdalyFormal.Round9.Guarded.QualitativeR2\nopen Set\n','namespace AdalyFormal.Round9.Guarded.QualitativeR2\nopen scoped RealInnerProductSpace')
vac=section(source,'noncomputable def vacEdge','def CanonicalCoupling')
line=section(source,'def KernelLine','/-- A concrete, compiled substitute')
color=section('AHP/round10/shared/dictionary/R4_ColorResponse.lean',
  '/-- Physical fine site on the left face of Omega0. -/', 'theorem half_pauliE1')
opens='''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
'''
text=prefix+'\n'+(HERE/'KernelStructure.lean').read_text().removeprefix('import D1IVT\n')
text+='\n'+psd+'\nnamespace AdalyFormal.Round9.Guarded.QualitativeR2\n'+opens+vac+'\nend AdalyFormal.Round9.Guarded.QualitativeR2\n'
text+='\nnamespace AdalyFormal.Round10.Assembly.R2\n'+opens+line+'\nend AdalyFormal.Round10.Assembly.R2\n'
text+='\nnamespace AdalyFormal.Round10.Dictionary.ColorObstruction\n'+opens+'''open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.D1Literal (sing sing_apply sing_apply_self)
'''+color+'\nend AdalyFormal.Round10.Dictionary.ColorObstruction\n'
text+='\n'+(HERE/'ActualAppendix.lean.txt').read_text()
(HERE/'ActualKernel.lean').write_text(text)
(HERE/'COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('wrote',HERE/'ActualKernel.lean',len(text.splitlines()),'lines')
