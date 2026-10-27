#!/usr/bin/env python3
"""Audit exact partial proofs and separate absent final compile evidence.
No numerical certificate and no pinned-goal closure is asserted.
"""
import ast, hashlib, json, re, sys
sys.dont_write_bytecode = True
from pathlib import Path
import mpmath as mp
mp.mp.dps=650
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PIN=ROOT/'AHP/round3/guarded/pin/Statement.lean'
BRIDGE=ROOT/'AHP/round5/guarded/ivt-r2/Attempt.lean'
PRIOR=ROOT/'AHP/round6/placement-r1/Attempt.lean'
ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def declarations(s):
    stack=[];out={};comment=0
    for n,line in enumerate(s.splitlines(),1):
        code='';i=0
        while i<len(line):
            if line[i:i+2]=='/-':comment+=1;i+=2
            elif comment and line[i:i+2]=='-/':comment-=1;i+=2
            elif comment:i+=1
            elif line[i:i+2]=='--':break
            else:code+=line[i];i+=1
        x=code.strip()
        m=re.match(r'^(namespace|section)(?:\s+(\S+))?$',x)
        if m:stack.append((m[1],m[2] or ''));continue
        if re.match(r'^end(?:\s+\S+)?$',x):stack.pop();continue
        m=re.match(r'^(?:noncomputable )?(?:abbrev|def|theorem)\s+([\w.\']+)',x)
        if m:
            name='.'.join([name for kind,name in stack if kind=='namespace']+[m[1]])
            assert name not in out,name
            out[name]=n
    assert not stack
    return out

def inspect_source(p):
    s=p.read_text()
    assert p.read_bytes().startswith(PIN.read_bytes()),p
    assert re.findall(r'^import (.+)$',s,re.M)==['DrEquiv'],p
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s),p
    return declarations(s)

def compile_record(p):
    names=inspect_source(p);lp=Path(str(p)+'.log');ep=Path(str(p)+'.exit')
    assert ep.read_text().strip()=='0',ep
    log=lp.read_text()
    assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:',log),lp
    rec=re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M)
    ax={n:[a.strip() for a in aa.split(',') if a.strip()] for n,aa in rec}
    assert all(set(a)<=ALLOWED for a in ax.values()),lp
    assert set(names)<=set(ax),set(names)-set(ax)
    assert p.stat().st_mtime_ns<=lp.stat().st_mtime_ns<=ep.stat().st_mtime_ns,p
    return dict(file=str(p.relative_to(ROOT)),exitCode=0,localDeclarations=len(names),
        dependencyRecords=len(rec),warningCount=0,sourceSha256=sha(p),logSha256=sha(lp)),ax

attempt=HERE/'Attempt.lean'
locals_final=inspect_source(attempt)
assert attempt.read_bytes().startswith(PRIOR.read_bytes())
assert attempt.read_bytes().startswith(BRIDGE.read_bytes())
# All new source sections are copied verbatim from the successfully checked
# HybridCertificate.lean; this is NOT a successful check of the concatenation.
marker='end AdalyFormal.Round6.Guarded.PlacementR1\n'
hybrid=(HERE/'HybridCertificate.lean').read_text()
suffix=hybrid[hybrid.index(marker)+len(marker):]
assert attempt.read_bytes()==PRIOR.read_bytes()+suffix.encode()
assert not Path(str(attempt)+'.exit').exists()
focused={};known={}
for file in ['SourceReduction.lean','HybridCertificate.lean']:
    focused[file],a=compile_record(HERE/file);known.update(a)
prior_rec,prior_ax=compile_record(PRIOR)
known.update(prior_ax)
assert set(locals_final)<=set(known)
main='AdalyFormal.Round6.Guarded.PlacementR2.hybrid_correction_formula'
assert main in known
# The complete interrupted source/log remain traceable; no fake exit is made.
interrupted=json.loads((HERE/'INTERRUPTED.json').read_text())
assert sha(HERE/'Interrupted.Attempt.lean')==interrupted['interruptedSourceSha256']
assert sha(HERE/'Interrupted.Attempt.lean.log')==interrupted['logSha256']
assert not (HERE/'Interrupted.Attempt.lean.exit').exists()

cases=[(1,'1e-3',0,0,100,180,'hybrid_q1_p100','hybrid_q1_p180'),
       (2,'1e-100',7,7,400,500,'hybrid_q2_p400','hybrid_q2_p500'),
       (2,'1e-220',7,7,500,600,'hybrid_q2_e220_p500','hybrid_q2_e220_p600')]
results=[]
for q,eps,iy,iz,plo,phi,taglo,taghi in cases:
    ds=[];ps=[]
    for precision,tag in [(plo,taglo),(phi,taghi)]:
        p=HERE/'b1_c-1'/f'q{q}_R18_e{eps}_p{precision}_s{iy}_{iz}.json'
        d=json.loads(p.read_text());ds.append(d);ps.append(p)
        assert (HERE/(tag+'.exit')).read_text().strip()=='0'
        assert d['boundary_sign']==1 and d['core_sign']==-1
        assert d['peak_rss_KiB']*1024<8_000_000_000
        assert d['first_crossing_status'].startswith('NOT CHECKED')
    low,high=ds;a=mp.mpf(low['pairing']);b=mp.mpf(high['pairing'])
    agreement=-mp.log10(abs((a-b)/b))
    assert agreement>70
    ratio=mp.mpf(high['augmented_kernel_max_residual'])/abs(b)
    assert ratio<mp.mpf('1e-70')
    results.append(dict(q=q,R=18,epsilon=eps,sector=[iy,iz],precisions=[plo,phi],
        pairing=mp.nstr(b,24),sign='positive' if b>0 else 'negative',
        relativeAgreementDigits=float(agreement),kernelResidualOverAbsolutePairing=mp.nstr(ratio,12),
        leftHalfMass=mp.nstr(mp.mpf(high['left_half_mass']),15),
        secondBoundarySchurEigenvalue=mp.nstr(mp.mpf(high['schur_eigenvalues'][1]),15),
        alternativeCorrectedTestForm=mp.nstr(mp.mpf(high['alternative_corrected_test_form']),15),
        maximumRSSKiB=max(d['peak_rss_KiB'] for d in ds),
        data=[dict(file=str(p.relative_to(HERE)),sha256=sha(p)) for p in ps],
        formalCertificate=False,firstFullCarrierCrossingChecked=False))
assert [r['sign'] for r in results]==['positive','negative','positive']
for p in HERE.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
report=dict(closedGoal='none',file=str(attempt.relative_to(ROOT)),exitCode=-1,
    mainDeclaration=main,mainLineInFinal=locals_final[main],mainAxioms=known[main],
    mainCompiledIn='AHP/round6/placement-r2/HybridCertificate.lean',
    mainLineInCompiledFile=declarations(hybrid)[main],
    finalSourceSha256=sha(attempt),pinVerbatim=True,round5BridgeVerbatim=True,
    placementR1Verbatim=True,newSectionsCopiedVerbatimFromSuccessfulFocusedCompile=True,
    finalCompilation='NO COMPLETION EVIDENCE. Interrupted call was not relaunched; assembled final file was not compiled as a whole.',
    interrupted=interrupted,focusedCompilations=focused,inheritedPriorCompilation=prior_rec,
    finalLocalDeclarations=len(locals_final),allFinalDeclarationsHaveIndividualPrintCommands=True,
    dependencyEvidence='Every declaration has allowed dependencies in a successful focused or prior file; not a final-file compile claim.',
    newDeclarations={n:l for n,l in locals_final.items() if '.PlacementR2.' in n},
    numericalCases=results,maximumRSSKiB=max(r['maximumRSSKiB'] for r in results),
    obstacle='Hybrid source is exactly unchanged by boundary placement. H and dressed C2 may still change. Selected-sector signs reverse again at tiny amplitude; no all-q,R closed-form sign, initial positivity proof or full-carrier first-crossing dictionary exists. No pinned goal is proved.')
(HERE/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
