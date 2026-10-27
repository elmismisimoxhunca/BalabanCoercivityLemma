#!/usr/bin/env python3
"""Audit compiled artifacts, not the unproved spectral hypothesis or numerics."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
source_path=HERE/'Attempt.lean'
source=source_path.read_text()
pin=ROOT/'AHP/round3/guarded/pin/Statement.lean'
previous=ROOT/'AHP/round4/guarded/refute-r1/Attempt.lean'
assert source_path.read_bytes().startswith(pin.read_bytes())
assert source_path.read_bytes().startswith(previous.read_bytes())
imports=re.findall(r'^import (.+)$',source,re.M)
assert imports==['DrEquiv']
forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source)
assert not forbidden
exit_path=HERE/'Attempt.lean.exit';log_path=HERE/'Attempt.lean.log'
assert exit_path.read_text().strip()=='0'
log=log_path.read_text()
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:',log)
records=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
allowed={'propext','Classical.choice','Quot.sound'}
for n,ax in records:
    assert {a.strip() for a in ax.split(',') if a.strip()}<=allowed,(n,ax)
local_decls=re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",source,re.M)
seen={n for n,_ in records}
assert all(any(n.endswith('.'+d) for n in seen) for d in local_decls)
assert source_path.stat().st_mtime_ns<=log_path.stat().st_mtime_ns<=exit_path.stat().st_mtime_ns
main='AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings'
assert main in seen
lines={d:i for i,l in enumerate(source.splitlines(),1)
       for d in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",l)}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
num=[]
for p in sorted((HERE/'numerics').glob('crossing_R*_eps*.json')):
    d=json.loads(p.read_text())
    assert d['peak_rss_kib']<2_000_000_000/1024
    num.append(dict(file=str(p.relative_to(ROOT)),sha256=sha(p),epsilon=d['epsilon'],R=d['R'],
                    peakRssKiB=d['peak_rss_kib'],projectedCorrectionEigenvalues=d['projected_D'][0]['eigenvalues']))
sectors=HERE/'numerics/sectors_R2.json'
s=json.loads(sectors.read_text());assert len(s['sectors'])==16
for f in ['crossing_R2','crossing_half','crossing_flipped','crossing_R6_AD','sectors_R2']:
    assert (HERE/'numerics'/f'{f}.exit').read_text().strip()=='0'
result=dict(closedGoal='none',file=str(source_path.relative_to(ROOT)),mainDeclaration=main,
 mainLine=lines[main.split('.')[-1]],
 axiomLine=next(f"'{n}' depends on axioms: [{', '.join(a.strip() for a in ax.split(',') if a.strip())}]" for n,ax in records if n==main),
 compileExit=0,warningCount=0,imports=imports,pinVerbatimBytePrefix=True,
 inheritedRound4AttemptVerbatimBytePrefix=True,sourceSha256=sha(source_path),pinSha256=sha(pin),
 inheritedAttemptSha256=sha(previous),logSha256=sha(log_path),
 localDeclarationCount=len(local_decls),printedDependencyRecords=len(records),
 allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,forbiddenTokens=forbidden,
 newDeclarations={n:l for n,l in lines.items() if l>len(previous.read_text().splitlines())},
 numericalRuns=num,sectorFileSha256=sha(sectors),sectorCount=16,
 numericalMinimumCarrierEigenvalue=s['minimum_carrier_eigenvalue'],
 scope='Conditional IVT reduction for actual curved-twist assemblies, with cofinal radius-before-cap bookkeeping. The arbitrarily small KernelPositiveCrossing premise is NOT proved. No pinned goal is closed; numerical signs are not certified.',
 independentReplay=False)
(HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
