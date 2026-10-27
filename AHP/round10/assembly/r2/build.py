#!/usr/bin/env python3
"""Compact actual-operator harness and verbatim-prefix assembly. Never compile Attempt here."""
from pathlib import Path
import re, json, hashlib
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
R9=REPO/'AHP/round9/qualitative-r2/Attempt.lean'
DICT=REPO/'AHP/round10/shared/dictionary/R1_Dictionary.lean'
manifest=[]
def decl(path,name):
    src=path.read_text()
    m=re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev|lemma) '+re.escape(name)+r'\b',src,re.M)
    assert m,(path,name)
    nxt=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |lemma |open |end |namespace |#print |/[-!])',src[m.end():])
    e=m.end()+nxt.start()+1 if nxt else len(src)
    out=src[m.start():e].rstrip()+'\n'
    manifest.append(dict(name=name,source=str(path.relative_to(REPO)),line=src[:m.start()].count('\n')+1,sha256=hashlib.sha256(out.encode()).hexdigest()))
    return out
base='''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
'''
r4='AdalyFormal.Round4.Guarded.RefuteR1'
r5='AdalyFormal.Round5.Guarded.IVTR2'
qual='AdalyFormal.Round9.Guarded.Qualitative'
q2='AdalyFormal.Round9.Guarded.QualitativeR2'
qj='AdalyFormal.Round9.Guarded.QualitativeR2Joint'
opens='open AdalyFormal.Round2.Guarded.Pin\n'
def ns(namespace,names,more='',path=R9):
    return '\nnamespace '+namespace+'\n'+base+more+'\nopen Classical\n'+\
        '\n'.join(decl(path,n) for n in names)+'\nend '+namespace+'\n'
parts=['import DrEquiv\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nset_option maxRecDepth 8000\n']
src=R9.read_text()
pin=src[src.index('namespace AdalyFormal.Round2.Guarded.Pin'):src.index('noncomputable def G1invS')]
parts += [pin,'\nend Ops\nend Selectors\nend AdalyFormal.Round2.Guarded.Pin\n']
parts.append(ns(r4,['dilLu','dilTower','dilLam','dilPattern'],opens))
opens+='open '+r4+'\n'
parts.append(ns(r5,['maskedU'],opens))
opens+='open '+r5+'\n'
parts.append(ns(qual,['pathU','pathP','pathA','uthPath','vacA'],opens))
opens+='open '+qual+'\n'
parts.append(ns(q2,['Ug_coe_uMat','bulkU','bulkP','bulkD','rotGauge','uθ_comm','uθ_conj','Ug_eq_uθ','rot_maskedU','rot_trivial','rot_bulkU','bulkD_rot'],opens+'open AdalyFormal.GaugeCov (adEL)\nopen AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)\n'))
parts.append(ns(qj,['corrDeriv'],opens))
parts.append(ns('AdalyFormal.Round9.Guarded.AnalyticR1',['TwistSpace'],opens))
# Three small round-9 pieces, kept in original namespaces and with identical bodies.
parts.append('namespace '+qual+'\nopen scoped RealInnerProductSpace\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'+decl(R9,'scalar_on_complex_line')+'\nend '+qual+'\n')
parts.append('namespace '+q2+'\nopen Set\nopen AdalyFormal.D1Literal (PSD)\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'+decl(R9,'psdEdge')+'\nend '+q2+'\n')
parts.append(ns(q2,['vacEdge','CanonicalCoupling'],opens))
parts.append(ns(qj,['CofinalAnyProfileCoupling'],opens))
# Only the R1 symmetry pieces consumed by our glue, not the 1345-line dictionary.
dictparts=['namespace AdalyFormal.Round10.Dictionary\nopen scoped RealInnerProductSpace\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'+decl(DICT,'comm_of_quad')+'\n'+decl(DICT,'deriv_comm')+'\nend AdalyFormal.Round10.Dictionary\n',
    ns('AdalyFormal.Round10.Dictionary.Actual',['bulkD_U1','corrDeriv_U1'],opens+'open '+q2+'\nopen '+qj+'\nopen AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)\nopen AdalyFormal.GaugeCov (adEL)\n',DICT)]
source=(REPO/'AHP/round10/shared/nonvanishing/R1_SourceDominance.lean').read_text().removeprefix('import D1IVT\n')
cofinal=(REPO/'AHP/round10/shared/assembly/R1_Cofinal.lean').read_text().removeprefix('import D1IVT\n')
freeprofile=(REPO/'AHP/round10/shared/nonvanishing/R2_SourceFamily.lean').read_text().removeprefix('import D1IVT\n')
common='\n'.join(dictparts+[source,cofinal,freeprofile,(HERE/'Appendix.lean').read_text()])
def write_changed(path,content):
    data=content.encode() if isinstance(content,str) else content
    if not path.exists() or path.read_bytes()!=data: path.write_bytes(data)
write_changed(HERE/'Compact.lean','\n'.join(parts)+'\n'+common)
# R2 dictionary pieces are already independently compiled in their own harness.
# Assemble them into the historical file without recompiling that large file.
half=ns('AdalyFormal.Round10.Dictionary',['half_rotation_matrix'],
    opens+'open AdalyFormal.D1Literal\n',DICT)
halfcopy=manifest.pop()
dictionary_r2='\n'.join([half]+[(REPO/'AHP/round10/dictionary/r2'/f).read_text().removeprefix('import DrEquiv\n')
    for f in ['PhaseSource.lean','KKT.lean','SourceAppendix.lean']])
write_changed(HERE/'DictionaryAppendix.lean',dictionary_r2)
write_changed(HERE/'DICTIONARY_APPENDIX_COPIES.json',json.dumps([halfcopy],indent=2)+'\n')
write_changed(HERE/'Attempt.lean',R9.read_bytes()+b'\n'+dictionary_r2.encode()+b'\n'+common.encode()+b'\n'+(HERE/'GoalBridge.lean').read_bytes())
write_changed(HERE/'COPIES.json',json.dumps(manifest,indent=2)+'\n')
print('Compact lines:',len((HERE/'Compact.lean').read_text().splitlines()))
print('Attempt prefix exact:',(HERE/'Attempt.lean').read_bytes().startswith(R9.read_bytes()),'(not compiled)')
