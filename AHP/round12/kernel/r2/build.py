#!/usr/bin/env python3
"""Build a compact actual-response package from verbatim frozen-round definitions."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
records=[]
def section(path,start,end):
    full=(ROOT/path).read_text(); a=full.index(start); b=full.index(end,a)
    text=full[a:b]
    records.append(dict(path=path,start=start,end=end,start_line=full[:a].count('\n')+1,
      sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
prefix=(ROOT/'AHP/round10/shared/dictionary/R3_FreeSource.lean').read_text()
records.append(dict(path='AHP/round10/shared/dictionary/R3_FreeSource.lean',entire_file=True,sha256=hashlib.sha256(prefix.encode()).hexdigest()))
assembly='AHP/round10/shared/assembly/R4_ResponseHull.lean'
oldkernel='AHP/round12/kernel/r1/ActualKernel.lean'
r1dict='AHP/round10/shared/dictionary/R1_Dictionary.lean'
opens='''open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
'''
def ns(name,body):return '\nnamespace '+name+'\n'+opens+body+'\nend '+name+'\n'
text=prefix+'\n'+(HERE/'LineResponse.lean').read_text().removeprefix('import DrEquiv\n')
text+=ns('AdalyFormal.Round9.Guarded.Qualitative',
 section(r1dict,'noncomputable def pathU','noncomputable def dilMask')+
 section(r1dict,'noncomputable def vacA','end AdalyFormal.Round9.Guarded.Qualitative'))
text+=section(oldkernel,'namespace AdalyFormal.Round9.Guarded.QualitativeR2\nopen Set\n','namespace AdalyFormal.Round10.Dictionary.ColorObstruction\n')
text+=ns('AdalyFormal.Round9.Guarded.QualitativeR2','variable {L : PeriodicLatticeExtent}\nopen AdalyFormal.D1Literal (SU2m)\n'+section(assembly,'def AnM ','end AdalyFormal.Round9.Guarded.QualitativeR2\n'))
text+='''\nnamespace AdalyFormal.Round10.Assembly.R4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
'''+section(assembly,'def responseHull ','theorem separator_of_notMem_responseHull')+'end AdalyFormal.Round10.Assembly.R4\n'
text+=ns('AdalyFormal.Round10.Assembly.R4',section(assembly,'abbrev ProfileSpace','theorem exists_positive_profile_iff_noCancellation')+
 section(assembly,'theorem responseGradient_ne_zero_iff','theorem curlDetected_of_noCancellation')+
 section(assembly,'def CofinalAnyPathNoResponseCancellation','theorem cofinalAnyProfileCoupling_iff_noCancellation'))
text+=ns('AdalyFormal.Round10.Assembly.R3','open AdalyFormal.Round10.Assembly.R2 (KernelLine)\n'+
 section(assembly,'def CofinalAnyPathCurlLine','theorem cofinalAnyProfileCoupling_of_curlLine'))
text+='\n'+(HERE/'ActualResponseAppendix.lean.txt').read_text()
(HERE/'ActualResponse.lean').write_text(text)
(HERE/'COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('wrote',len(text.splitlines()),'lines')
