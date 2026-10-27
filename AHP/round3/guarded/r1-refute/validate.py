#!/usr/bin/env python3
"""Artifact audit only; no Lean invocation and no semantic proof by Python."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
source=(HERE/'Attempt.lean').read_text()
pin=(HERE.parent/'pin/Statement.lean').read_text()
assert source.startswith(pin), 'pin was not retained verbatim'
assert re.findall(r'^import (.+)$',source,re.M)==['DrEquiv']
forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',source)
assert not forbidden,forbidden
assert (HERE/'Attempt.lean.exit').read_text().strip()=='0'
log=(HERE/'Attempt.lean.log').read_text()
assert not re.search(r'\berror:',log),log[-5000:]
warning_count=len(re.findall(r'\bwarning:',log))
records=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.S)
allowed={'propext','Classical.choice','Quot.sound'}
assert records
for name,axs in records:
    names={x.strip() for x in axs.split(',') if x.strip()}
    assert names<=allowed,(name,names)
# Every authored named declaration, including the copied pin and support appendix.
names=re.findall(r'^(?:noncomputable )?(?:abbrev|def|theorem)\s+([A-Za-z0-9_\.]+)',source,re.M)
seen={name for name,_ in records}
missing=[name for name in names if not any(n.endswith('.'+name) for n in seen)]
assert not missing,missing
main='AdalyFormal.Round3.Guarded.RefuteR1.probe_not_negative_witness'
assert main in seen
assert (HERE/'Attempt.lean').stat().st_mtime <= (HERE/'Attempt.lean.log').stat().st_mtime
assert (HERE/'Attempt.lean.log').stat().st_mtime <= (HERE/'Attempt.lean.exit').stat().st_mtime
assert (HERE/'numerics/collar_probe.exit').read_text().strip()=='0'
numeric=json.loads((HERE/'numerics/collar_results.json').read_text())
assert [r['R'] for r in numeric['results']]==[2,6,18]
for row in numeric['results']:
    R=row['R']; geo=row['geometry']
    assert geo['fine_lift_sides']==[4*R+16,8,8]
    assert geo['Om0']==[4,4*R+8]
    assert geo['Om1']==[2*R+4,2*R+8]
assert max(r['peak_rss_kib'] for r in numeric['results'])*1024 < 2_000_000_000
ns='AdalyFormal.Round3.Guarded.RefuteR1.'
lines={name:i for i,line in enumerate(source.splitlines(),1)
       for name in re.findall(r'^(?:noncomputable )?(?:abbrev|def|theorem)\s+([A-Za-z0-9_\.]+)',line)}
result=dict(closedGoal='none',file=str((HERE/'Attempt.lean').relative_to(ROOT)),
    mainDeclaration=main,mainLine=lines['probe_not_negative_witness'],
    compileExit=0,warningCount=warning_count,pinVerbatimBytePrefix=True,imports=['DrEquiv'],forbiddenTokens=[],
    sourceSha256=hashlib.sha256(source.encode()).hexdigest(),
    pinSha256=hashlib.sha256(pin.encode()).hexdigest(),
    localDeclarationCount=len(names),printedDependencyRecords=len(records),
    allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,
    ownDeclarations={k:v for k,v in lines.items() if v>len(pin.splitlines())},
    mainAxiomLine=next(f"'{name}' depends on axioms: [{axs}]" for name,axs in records if name==main),
    numericalExit=0,numericalGeometryMatchesProbeDefinitions=True,numericalMaxRssKiB=max(r['peak_rss_kib'] for r in numeric['results']),
    notes='No target closed; candidate exclusion, not an in-class spectral certificate. No independent replay.')
(HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
