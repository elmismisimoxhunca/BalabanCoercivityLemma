#!/usr/bin/env python3
"""Artifact checks, not a numerical certificate or a pinned-goal proof."""
import ast, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
src=HERE/'Attempt.lean'
pin=ROOT/'AHP/round3/guarded/pin/Statement.lean'
bridge=ROOT/'AHP/round5/guarded/ivt-r2/Attempt.lean'
s=src.read_text()
assert src.read_bytes().startswith(pin.read_bytes())
assert src.read_bytes().startswith(bridge.read_bytes())
assert re.findall(r'^import (.+)$',s,re.M)==['DrEquiv']
assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s)
# Resolve LOCAL declaration names through actual namespaces, not suffix matches.
stack=[];local={};in_comment=0
for lineno,line in enumerate(s.splitlines(),1):
    # Block comments do not carry declarations; support nested Lean comments.
    code='';i=0
    while i<len(line):
        if line[i:i+2]=='/-':in_comment+=1;i+=2
        elif in_comment and line[i:i+2]=='-/':in_comment-=1;i+=2
        elif in_comment:i+=1
        elif line[i:i+2]=='--':break
        else:code+=line[i];i+=1
    x=code.strip()
    m=re.match(r'^(namespace|section)(?:\s+(\S+))?$',x)
    if m:stack.append((m[1],m[2] or ''));continue
    if re.match(r'^end(?:\s+\S+)?$',x):
        assert stack,(lineno,x)
        stack.pop();continue
    m=re.match(r'^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.\']+)',x)
    if m:
        n='.'.join([name for kind,name in stack if kind=='namespace']+[m[1]])
        assert n not in local,n
        local[n]=lineno
assert not stack
allowed={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
logs={}
for file in ['Attempt.lean','Attempt.verify.lean']:
    p=HERE/file;lp=HERE/(file+'.log');ep=HERE/(file+'.exit')
    assert p.read_bytes()==src.read_bytes()
    assert ep.read_text().strip()=='0'
    log=lp.read_text()
    assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:',log)
    rec=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
    records={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in rec}
    assert all(set(a)<=allowed for a in records.values())
    assert set(local)<=set(records),set(local)-set(records)
    assert p.stat().st_mtime_ns<=lp.stat().st_mtime_ns<=ep.stat().st_mtime_ns
    logs[file]=dict(exitCode=0,warningCount=0,dependencyRecords=len(rec),logSha256=sha(lp),
        mainAxioms=records['AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero'])
nums=[]
for q,eps,precisions in [(1,'1e-3',[80,160]),(2,'1e-100',[160,240])]:
    for dps in precisions:
        p=HERE/f'placement_q{q}_R18_e{eps}_p{dps}.json';d=json.loads(p.read_text())
        assert (HERE/f'probe_q{q}_p{dps}.exit').read_text().strip()=='0'
        assert d['source_outside_level0']==[] and d['source_nonzero_count']==12
        for k in ['exact_KKT_candidate_residual','maximum_computed_positive_level_HtJ',
                  'KKT_solve_relative_residual','arbitrary_test_correction_computed',
                  'arbitrary_test_correction_exact_candidate']:
            assert d[k]=='0.0',(p,k,d[k])
        assert d['peak_rss_KiB']*1024 < 8_000_000_000
        nums.append(dict(file=p.name,sha256=sha(p),q=q,epsilon=eps,dps=dps,
            peakRSSKiB=d['peak_rss_KiB'],positivePairing=False,certified=False))
for p in HERE.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
new={n:l for n,l in local.items() if l>len(bridge.read_text().splitlines())}
out=dict(closedGoal='none',file=str(src.relative_to(ROOT)),
    mainDeclaration='AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero',
    mainLine=local['AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero'],
    pinVerbatimBytePrefix=True,round5BridgeVerbatimBytePrefix=True,
    soleImport='DrEquiv',sourceSha256=sha(src),pinSha256=sha(pin),bridgeSha256=sha(bridge),
    localDeclarations=len(local),allLocalDeclarationsPrinted=True,allAxiomsAllowed=True,
    compileEvidence=logs,newDeclarations=new,numericalRuns=nums,
    replay='Byte-identical builder replay; not an independent judge replay.',
    obstacle='The relocated curvature is supported on linear level-zero constraints. The genuine correction is exactly zero; boundary-only masks separated by three sites from Omega1 cannot separate A and A-D. No pinned goal is closed.')
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
