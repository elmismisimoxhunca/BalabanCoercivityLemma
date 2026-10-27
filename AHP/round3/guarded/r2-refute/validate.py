#!/usr/bin/env python3
"""Artifact consistency audit, not a substitute for the Lean kernel or numerics."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
source=(HERE/'Attempt.lean').read_text()
pin=(HERE.parent/'pin/Statement.lean').read_text()
assert source.startswith(pin), 'pin differs'
assert re.findall(r'^import (.+)$',source,re.M)==['DrEquiv']
assert not re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source)
assert (HERE/'Attempt.lean.exit').read_text().strip()=='0'
log=(HERE/'Attempt.lean.log').read_text()
assert not re.search(r'\b(?:error|warning):',log)
records=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
allowed={'propext','Classical.choice','Quot.sound'}
assert records
for name,axs in records:
    assert {a.strip() for a in axs.split(',') if a.strip()}<=allowed,(name,axs)
locals_=re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",source,re.M)
seen={name for name,_ in records}
assert all(any(n.endswith('.'+name) for n in seen) for name in locals_)
main='AdalyFormal.Round3.Guarded.RefuteR2.wide_probe_geometry_and_competitor'
assert main in seen
assert (HERE/'Attempt.lean').stat().st_mtime <= (HERE/'Attempt.lean.log').stat().st_mtime <= (HERE/'Attempt.lean.exit').stat().st_mtime
num=HERE/'numerics'
for name in ('wide_probe','smallness_probe','corrected_probe'):
    assert (num/(name+'.exit')).read_text().strip()=='0'
wide=json.loads((num/'wide_results.json').read_text())
small=json.loads((num/'smallness_results.json').read_text())
corrected=json.loads((num/'corrected_results.json').read_text())
assert len(corrected['results'])==2
assert [r['R'] for r in wide['results']]==[2,4,6]
assert len(small['results'])==6
for row in wide['results']+small['results']+corrected['results']:
    R=row['R'];g=row['geometry']
    assert g['fine_lift_sides']==[12*R+16,8,8]
    assert g['Om0']==[4,12*R+12]
    assert g['Om1']==[2*R+4,10*R+12]
    assert g['Lambda']==[3*R+4,3*R+6]
    assert row['peak_rss_kib']*1024<2_000_000_000
    if 'kernel_residual_norm' in row:
        assert row['kernel_residual_norm']<1e-8
    else:
        assert row['full_quotient_kernel_residual']<1e-8
        assert row['full_quotient_carrier_lowest_six_at_corrected'][0]>0
        assert row['checks']['directional_difference']<1e-9
    for key in ('torus_arithmetic','base_law','block0','block1','collar','site_cover','plaq_cover','lambda_block_arithmetic','lambda_subset','lambda_collar'):
        assert g[key],(R,key)
for name in ('assembly.py','delta_ops.py'):
    assert (num/name).read_bytes()==(HERE.parent/'r1-refute/numerics'/name).read_bytes()
lines={name:i for i,line in enumerate(source.splitlines(),1) for name in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",line)}
result=dict(closedGoal='none',file=str((HERE/'Attempt.lean').relative_to(ROOT)),
 mainDeclaration=main,mainLine=lines[main.split('.')[-1]],
 mainAxiomLine=next(f"'{n}' depends on axioms: [{', '.join(a.strip() for a in axs.split(','))}]" for n,axs in records if n==main),
 compileExit=0,warningCount=0,imports=['DrEquiv'],pinVerbatimBytePrefix=True,
 pinSha256=hashlib.sha256(pin.encode()).hexdigest(),sourceSha256=hashlib.sha256(source.encode()).hexdigest(),
 localDeclarationCount=len(locals_),printedDependencyRecords=len(records),
 allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,forbiddenTokens=[],
 ownDeclarations={n:i for n,i in lines.items() if i>len(pin.splitlines())},
 numericalExitCodes={'wide_probe':0,'smallness_probe':0,'corrected_probe':0},
 numericalMaxRssKiB=max(r['peak_rss_kib'] for r in wide['results']+small['results']+corrected['results']),
 numericalScriptSha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(num.glob('*.py'))},
 numericalGeometryMatchesDefinitions=True,
 notes='New admissible geometry and positive-energy competitor only; no coverage/regularity theorem or exact spectral separation. No independent second-agent replay.')
(HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
