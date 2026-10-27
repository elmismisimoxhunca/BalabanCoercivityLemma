#!/usr/bin/env python3
"""Build a small harness with verbatim named declarations from round 9.
No earlier file is changed. The large historical concatenation is not retried.
"""
from pathlib import Path
import re, json, hashlib
root = Path(__file__).resolve().parent
repo = root.parents[3]
srcpath = repo / 'AHP/round9/qualitative-r2/Attempt.lean'
src = srcpath.read_text()
manifest = []
def decl(name):
    m = re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev) ' + re.escape(name) + r'\b', src, re.M)
    assert m, name
    nxt = re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |open |end |namespace |#print |/[-!])', src[m.end():])
    e = m.end() + nxt.start() + 1 if nxt else len(src)
    val = src[m.start():e].rstrip() + '\n'
    manifest.append(dict(name=name, source=str(srcpath.relative_to(repo)), line=src[:m.start()].count('\n')+1,
                         sha256=hashlib.sha256(val.encode()).hexdigest()))
    return val
baseopens = '''open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
'''
parts = ['import DrEquiv\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nset_option maxRecDepth 8000\n']
# Operative selector declarations are copied as a contiguous fragment, with original sections.
pin = src[src.index('namespace AdalyFormal.Round2.Guarded.Pin'):src.index('noncomputable def G1invS')]
parts += [pin, '\nend Ops\nend Selectors\nend AdalyFormal.Round2.Guarded.Pin\n']
def ns(name, names, opens='', classical=False):
    return '\nnamespace '+name+'\n'+baseopens+opens+('\nopen Classical\n' if classical else '')+'\n'+\
        '\n'.join(decl(n) for n in names)+'\nend '+name+'\n'
r4 = 'AdalyFormal.Round4.Guarded.RefuteR1'
r5a = 'AdalyFormal.Round5.Guarded.IVTR1'
r5b = 'AdalyFormal.Round5.Guarded.IVTR2'
qual = 'AdalyFormal.Round9.Guarded.Qualitative'
q2 = 'AdalyFormal.Round9.Guarded.QualitativeR2'
q2j = 'AdalyFormal.Round9.Guarded.QualitativeR2Joint'
pinopen = 'open AdalyFormal.Round2.Guarded.Pin\n'
opens = pinopen+'open '+r4+'\n'
parts.append(ns(r4, ['dilLu','dilTower','dilLam','dil_unit_size','dil_fine_size','dilPattern','dilU'],pinopen,True))
parts.append(ns(r5a,['twistU'],opens))
parts.append(ns(r5b,['maskedU'],opens,True))
opens += 'open '+r5a+'\nopen '+r5b+'\n'
parts.append(ns(qual,['pathU','pathP','pathA','uthPath','dilMask','vacA'],opens,True))
opens += 'open '+qual+'\n'
parts.append(ns(q2,['Ug_coe_uMat','bulkU','bulkP','bulkD'],opens))
parts += [(root/'Gauge.lean').read_text().removeprefix('import DrEquiv\n'),
          (root/'Translation.lean').read_text().removeprefix('import DrEquiv\n')]
# Exact earlier U(1) proof blocks; Ginv_all_gauge is supplied by the compiled dictionary core.
parts.append(ns(q2,['rotGauge','uθ_comm','uθ_conj','Ug_eq_uθ','rot_maskedU','rot_uthPath','rot_trivial',
                   'rot_pathU','rot_bulkU','vacA_rot','bulkD_rot'],opens+
                'open AdalyFormal.GaugeCov (adEL)\nopen AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)\n'+
                'open AdalyFormal.Round10.Dictionary (Ginv_all_gauge)\n'))
parts.append(ns(q2j,['corrDeriv'],opens))
parts.append(ns('AdalyFormal.Round9.Guarded.AnalyticR1',['TwistSpace'],opens))
symm = (repo/'AHP/round6/closedform-r1/Attempt.lean').read_text()
start = symm.index('namespace AdalyFormal.Round6.Guarded.ClosedFormR1')
marker = '#print axioms twoSite_exact_symmetry'
end = symm.index(marker,start)+len(marker)
parts += [symm[start:end]+'\nend AdalyFormal.Round6.Guarded.ClosedFormR1\n',
          (root/'ActualAppendix.lean').read_text()]
(root/'Actual.lean').write_text('\n'.join(parts))
(root/'COPIES.json').write_text(json.dumps(manifest,indent=2)+'\n')
