from pathlib import Path
import re, json, hashlib
ROOT=Path('AHP/round10/dictionary/r4')
records=[]
def fragment(path,start,end):
 s=Path(path).read_text(); i=s.index(start); j=s.index(end,i)
 z=s[i:j]
 records.append({'source':path,'start':s[:i].count('\n')+1,'endExclusive':s[:j].count('\n')+1,'sha256':hashlib.sha256(z.encode()).hexdigest()})
 return z
header='''import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
'''
half=fragment('AHP/round10/shared/dictionary/R3_FreeSource.lean','theorem half_rotation_matrix','end AdalyFormal.Round10.Dictionary\n')
flip=fragment('AHP/round9/qualitative-r2/Appendix.lean','theorem flipMat_mem','theorem flip_conj_uMat')
neutral=fragment('AHP/round10/shared/dictionary/R3_FreeSource.lean','def neutralCoord (X : SuTwo)','theorem neutralSource_component')
common='''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
'''
copies=(f'namespace AdalyFormal.Round10.Dictionary\n{common}\n'+half+'end AdalyFormal.Round10.Dictionary\n\n'+
 f'namespace AdalyFormal.Round9.Guarded.QualitativeR2\n{common}\n'+flip+'end AdalyFormal.Round9.Guarded.QualitativeR2\n\n'+
 f'namespace AdalyFormal.Round10.Dictionary.Source\n{common}\n'+neutral+'end AdalyFormal.Round10.Dictionary.Source\n')
body=(ROOT/'ColorAppendix.lean').read_text()
names=re.findall(r'^(?:theorem|def) (\w+)',body,re.M)
prints='\n'.join('#print axioms AdalyFormal.Round10.Dictionary.Color.'+x for x in names)+'\n'
(ROOT/'Color.lean').write_text(header+copies+body+prints)
(ROOT/'COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
print('Color:',len((header+copies+body+prints).splitlines()),'lines;',len(names),'new declarations')
if (ROOT/'ResponseAppendix.lean').exists():
 response=(ROOT/'ResponseAppendix.lean').read_text()
 rn=re.findall(r'^(?:theorem|def) (\w+)',response,re.M)
 rp='\n'.join('#print axioms AdalyFormal.Round10.Dictionary.ColorResponse.'+x for x in rn)+'\n'
 prefix=Path('AHP/round10/shared/dictionary/R3_FreeSource.lean').read_text()
 text=prefix+'\nnamespace AdalyFormal.Round9.Guarded.QualitativeR2\n'+common+flip+'end AdalyFormal.Round9.Guarded.QualitativeR2\n'+body+prints+response+rp
 if (ROOT/'ObstructionAppendix.lean').exists():
  geo=fragment('AHP/round5/guarded/ivt-r2/Attempt.lean','theorem dil_unit_size','theorem dil_fine_bound')
  obs=(ROOT/'ObstructionAppendix.lean').read_text()
  on=re.findall(r'^(?:theorem|def) (\w+)',obs,re.M)
  op='\n'.join('#print axioms AdalyFormal.Round10.Dictionary.ColorObstruction.'+x for x in on)+'\n'
  text+='\nnamespace AdalyFormal.Round4.Guarded.RefuteR1\nopen AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane\n'+geo+'end AdalyFormal.Round4.Guarded.RefuteR1\n'+obs+op
 (ROOT/'Actual.lean').write_text(text)
 (ROOT/'COPIES.json').write_text(json.dumps(records,indent=2)+'\n')
 print('Actual:',len(text.splitlines()),'lines;',len(rn),'new response declarations')
