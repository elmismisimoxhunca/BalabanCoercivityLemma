#!/usr/bin/env python3
"""Artifact audit; does not certify floating-point spectra or the open goals."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
lean=HERE/'Attempt.lean';source=lean.read_text()
pin=HERE.parent/'pin/Statement.lean'
previous=HERE.parent/'r2-refute/Attempt.lean'
assert lean.read_bytes().startswith(pin.read_bytes()),'pin differs'
assert lean.read_bytes().startswith(previous.read_bytes()),'inherited geometry differs'
assert re.findall(r'^import (.+)$',source,re.M)==['DrEquiv']
assert not re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source)
assert (HERE/'Attempt.lean.exit').read_text().strip()=='0'
log=(HERE/'Attempt.lean.log').read_text()
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:',log)
records=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
allowed={'propext','Classical.choice','Quot.sound'}
for name,axs in records:
    assert {a.strip() for a in axs.split(',') if a.strip()}<=allowed,(name,axs)
local_decls=re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",source,re.M)
seen={n for n,_ in records}
assert all(any(n.endswith('.'+d) for n in seen) for d in local_decls)
main='AdalyFormal.Round3.Guarded.RefuteR3.wide_in_class_nonflat_competitor'
assert main in seen
assert lean.stat().st_mtime <= (HERE/'Attempt.lean.log').stat().st_mtime <= (HERE/'Attempt.lean.exit').stat().st_mtime
num=HERE/'numerics'
for f in ['lift_probe','lift_single','primitive_lift_check']:
    assert (num/(f+'.exit')).read_text().strip()=='0'
lifts=[json.loads((num/f).read_text()) for f in ['lift_results.json','lift_single_results.json']]
for data in lifts:
    assert len(data['sectors'])==16
    assert {tuple(r['sector']) for r in data['sectors']}=={(i,j) for i in range(4) for j in range(4)}
    assert data['total_fiber_dimension']==18624
    assert data['zero_sector_jacobian_difference']<1e-8
    assert data['minimum_carrier_abs_over_all_sectors']>0
    assert all(r['negative_count']==0 for r in data['sectors'])
    assert all(r['hermitian_error']<1e-10 for r in data['sectors'])
    assert data['peak_rss_kib']*1024<2_000_000_000
    c=data['candidate'];g=c['geometry'];R=c['R']
    assert g['fine_lift_sides']==[12*R+16,8,8]
    assert g['Om0']==[4,12*R+12] and g['Om1']==[2*R+4,10*R+12]
    assert g['Lambda']==[3*R+4,3*R+6]
    assert c['full_quotient_kernel_residual']<1e-8
    assert c['checks']['hessian_refinement_norm']>data['minimum_carrier_abs_over_all_sectors'], 'reassess uncertainty text'
primitive=json.loads((num/'primitive_lift_results.json').read_text())
assert primitive['full_fine_bonds']==7680 and primitive['full_raw_output_rows']==592
assert all(r['differences'][-1]['max_absolute_error']<1e-8 for r in primitive['checks'])
assert primitive['peak_rss_kib']*1024<2_000_000_000
for name in ['assembly.py','delta_ops.py','wide_probe.py','corrected_probe.py']:
    assert (num/name).read_bytes()==(HERE.parent/'r2-refute/numerics'/name).read_bytes()
lines={d:i for i,line in enumerate(source.splitlines(),1)
       for d in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",line)}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=dict(closedGoal='none',file=str(lean.relative_to(ROOT)),mainDeclaration=main,
 mainLine=lines[main.split('.')[-1]],
 mainAxiomLine=next(f"'{n}' depends on axioms: [{', '.join(a.strip() for a in axs.split(','))}]" for n,axs in records if n==main),
 compileExit=0,warningCount=0,imports=['DrEquiv'],pinVerbatimBytePrefix=True,
 previousAttemptVerbatimBytePrefix=True,pinSha256=sha(pin),sourceSha256=sha(lean),
 localDeclarationCount=len(local_decls),printedDependencyRecords=len(records),
 allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,forbiddenTokens=[],
 ownDeclarations={n:i for n,i in lines.items() if i>len(previous.read_text().splitlines())},
 numericalExitCodes={'lift_probe':0,'lift_single':0,'primitive_lift_check':0},
 numericalMaxRssKiB=max([d['peak_rss_kib'] for d in lifts]+[primitive['peak_rss_kib']]),
 numericalScriptSha256={p.name:sha(p) for p in sorted(num.glob('*.py'))},
 numericalResultSha256={p.name:sha(p) for p in sorted(num.glob('*results.json'))},
 notes='Exact coverage, regularity, capped positive parameters, geometry, competitor and base nonidentity for the one-defect family at fixed m=1. No exact spectral separation or cofinal m. Fourier-sector computations and primitive checks are evidence only. No independent second-agent replay.')
(HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
