#!/usr/bin/env python3
"""Artifact audit. It does not prove InitialKernelControl or certify numerics."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
src=HERE/'Attempt.lean'; pin=ROOT/'AHP/round3/guarded/pin/Statement.lean'
old=ROOT/'AHP/round5/guarded/ivt-r1/Attempt.lean'
s=src.read_text(); logp=HERE/'Attempt.lean.log'; ex=HERE/'Attempt.lean.exit'
assert src.read_bytes().startswith(pin.read_bytes())
assert src.read_bytes().startswith(old.read_bytes())
imports=re.findall(r'^import (.+)$',s,re.M)
assert imports==['DrEquiv']
banned=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s)
assert not banned
assert ex.read_text().strip()=='0'
log=logp.read_text()
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:',log)
rec=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
allowed={'propext','Classical.choice','Quot.sound'}
for n,ax in rec:
    assert {a.strip() for a in ax.split(',') if a.strip()}<=allowed,(n,ax)
decls=re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",s,re.M)
seen={n for n,_ in rec}
assert all(any(n.endswith('.'+d) for n in seen) for d in decls)
assert src.stat().st_mtime_ns<=logp.stat().st_mtime_ns<=ex.stat().st_mtime_ns
main='AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control'
assert main in seen
lines={d:i for i,l in enumerate(s.splitlines(),1)
    for d in re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.']+)",l)}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
num=[]
for stem in ['smallcap','two_sided_R6']:
    assert (HERE/'numerics'/f'{stem}.exit').read_text().strip()=='0'
for name in ['crossing_R2_eps0.000195313.json','two_sided_R6_eps0.0015625.json']:
    p=HERE/'numerics'/name;d=json.loads(p.read_text())
    assert d['peak_rss_kib']*1024<2_000_000_000
    num.append(dict(file=str(p.relative_to(ROOT)),sha256=sha(p),epsilon=d['epsilon'],R=d['R'],
        peakRssKiB=d['peak_rss_kib'],projectedCorrectionEigenvalues=d['projected_D'][0]['eigenvalues'],
        carrierResidualNorm=d['kernel_residual_norm'],certified=False,
        variant=d.get('variant','Original single-defect dilU transcription')))
out=dict(closedGoal='none',file=str(src.relative_to(ROOT)),mainDeclaration=main,mainLine=lines[main.split('.')[-1]],
    axiomLine=next(f"'{n}' depends on axioms: [{', '.join(a.strip() for a in ax.split(',') if a.strip())}]" for n,ax in rec if n==main),
    compileExit=0,warningCount=0,imports=imports,pinVerbatimBytePrefix=True,
    previousRoundVerbatimBytePrefix=True,sourceSha256=sha(src),pinSha256=sha(pin),previousSha256=sha(old),
    logSha256=sha(logp),localDeclarationCount=len(decls),printedDependencyRecords=len(rec),
    allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,forbiddenTokens=banned,
    newDeclarations={n:l for n,l in lines.items() if l>len(old.read_text().splitlines())},
    numericalRuns=num,independentReplay=False,
    scope='Exact curved negative endpoint and first-crossing topology, arbitrary-mask class family, conditional cofinal reduction. Initial positivity and exact kernel correction sign remain unproved.')
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
