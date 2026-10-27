#!/usr/bin/env python3
"""Compact verbatim-definition harness. Writes only this round's files."""
from pathlib import Path
import re, hashlib, json
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
manifest = []

def decl(path, name):
    src = (ROOT/path).read_text()
    pat = r'^(?:(?:noncomputable )?(?:def|abbrev)|theorem) ' + re.escape(name) + r'\b'
    m = re.search(pat, src, re.M)
    assert m, (path, name)
    nxt = re.search(r'\n(?:(?:noncomputable )?(?:def |abbrev )|theorem |open |end |namespace |#print |/[-!])', src[m.end():])
    end = m.end() + nxt.start() + 1 if nxt else len(src)
    val = src[m.start():end].rstrip()+'\n'
    manifest.append(dict(source=path,name=name,line=src[:m.start()].count('\n')+1,sha256=hashlib.sha256(val.encode()).hexdigest()))
    return val

r1='AHP/round10/shared/dictionary/R1_Dictionary.lean'
a9='AHP/round9/analytic-r2/Attempt.lean'
q9='AHP/round9/qualitative-r2/Attempt.lean'
opens='''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
'''
parts=['import DrEquiv\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nset_option maxRecDepth 8000\n']
src=(ROOT/r1).read_text()
start=src.index('namespace AdalyFormal.Round2.Guarded.Pin')
end=src.index('end AdalyFormal.Round2.Guarded.Pin')+len('end AdalyFormal.Round2.Guarded.Pin')
parts.append(src[start:end]+'\n')
manifest.append(dict(source=r1,fragment='selector namespace',line=src[:start].count('\n')+1,sha256=hashlib.sha256((src[start:end]+'\n').encode()).hexdigest()))

def ns(name, path, names, extra=''):
    parts.append('\nnamespace '+name+'\n'+opens+extra+'\nopen Classical\n'+ '\n'.join(decl(path,n) for n in names)+'\nend '+name+'\n')
    # Audit copied declarations as well.
    parts.extend('#print axioms '+name+'.'+n+'\n' for n in names)

r4='AdalyFormal.Round4.Guarded.RefuteR1'
r5='AdalyFormal.Round5.Guarded.IVTR2'
q='AdalyFormal.Round9.Guarded.Qualitative'
q2='AdalyFormal.Round9.Guarded.QualitativeR2'
a1='AdalyFormal.Round9.Guarded.AnalyticR1'
a2='AdalyFormal.Round9.Guarded.AnalyticR2'
extra='open AdalyFormal.Round2.Guarded.Pin\n'
ns(r4,r1,['dilLu','dilTower','dilLam','dilPattern','dilU'],extra)
extra+='open '+r4+'\n'
ns(r5,r1,['maskedU'],extra)
extra+='open '+r5+'\n'
ns(q,r1,['dilMask'],extra)
extra+='open '+q+'\n'
ns(q2,r1,['Ug_coe_uMat','bulkU','bulkP','rotGauge','uθ_comm','uθ_conj','Ug_eq_uθ','rot_maskedU','rot_trivial','rot_bulkU'],extra)
ns('AdalyFormal.Round9.Guarded.QualitativeR2Joint',q9,['bulkU_dilMask'],extra+'open '+q2+'\n')
ns(a1,r1,['TwistSpace'],extra)
extra+='open '+a1+'\n'
ns(a2,a9,['dataFam','dilV','flatData','vacCoupling','IsSourceDerivative'],extra)
ns('AdalyFormal.Round10.Dictionary',r1,['half_rotation_matrix'],extra+'open AdalyFormal.D1Literal\n')
parts.append((HERE/'PhaseSource.lean').read_text().removeprefix('import DrEquiv\n'))
parts.append((HERE/'KKT.lean').read_text().removeprefix('import DrEquiv\n'))
parts.append((HERE/'SourceAppendix.lean').read_text())
(HERE/'Source.lean').write_text('\n'.join(parts))
(HERE/'COPIES.json').write_text(json.dumps(manifest,indent=2)+'\n')
