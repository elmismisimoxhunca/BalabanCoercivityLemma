#!/usr/bin/env python3
"""Artifact audit only: compilation does not prove the open cofinal premise."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'AHP/round10/dictionary/r4'
SH=ROOT/'AHP/round10/shared/dictionary'
allowed={'propext','Classical.choice','Quot.sound'}
new={}
for f,ns in [('ColorAppendix.lean','Color'),('ResponseAppendix.lean','ColorResponse'),('ObstructionAppendix.lean','ColorObstruction')]:
 new[ns]=['AdalyFormal.Round10.Dictionary.'+ns+'.'+n for n in re.findall(r'^(?:theorem|def) (\w+)',(OUT/f).read_text(),re.M)]
files=[(OUT/'Color.lean',['Color']),(OUT/'Actual.lean',list(new)),(SH/'R4_ColorSelection.lean',['Color']),(SH/'R4_ColorResponse.lean',list(new))]
checks=[]
for f,groups in files:
 s=f.read_text();lp=Path(str(f)+'.log');ep=Path(str(f)+'.exit');log=lp.read_text()
 records={m.group(1):[x.strip() for x in (m.group(2) or '').split(',') if x.strip()] for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)}
 expected=sum((new[g] for g in groups),[])
 c={'path':str(f.relative_to(ROOT)),'lines':len(s.splitlines()),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
 'logSha256':hashlib.sha256(lp.read_bytes()).hexdigest(),'exitCode':int(ep.read_text()),'fresh':f.stat().st_mtime<=lp.stat().st_mtime<=ep.stat().st_mtime,
 'imports':re.findall(r'^import (.+)$',s,re.M),'diagnostics':re.findall(r'^.*(?:error(?:\(|:)|warning:|sorryAx).*$',log,re.M),
 'prohibited':re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s),
 'recordCount':len(records),'newDeclarationCount':len(expected),'missingPrints':[d for d in expected if d not in records],
 'nonstandard':{k:v for k,v in records.items() if not set(v)<=allowed},'rawAxiomRecords':records}
 c['pass']=c['exitCode']==0 and c['fresh'] and c['imports']==['DrEquiv'] and not any(c[k] for k in ('diagnostics','prohibited','missingPrints','nonstandard'))
 checks.append(c)
copies=[]
for r in json.loads((OUT/'COPIES.json').read_text()):
 lines=(ROOT/r['source']).read_text().splitlines(keepends=True)
 frag=''.join(lines[r['start']-1:r['endExclusive']-1])
 copies.append({'source':r['source'],'start':r['start'],'endExclusive':r['endExclusive'],
 'pass':hashlib.sha256(frag.encode()).hexdigest()==r['sha256'] and frag in (OUT/'Actual.lean').read_text()})
old=ROOT/'AHP/round10/shared/dictionary/R3_FreeSource.lean'
prefix={'source':str(old.relative_to(ROOT)),'sha256':hashlib.sha256(old.read_bytes()).hexdigest(),
 'pass':(OUT/'Actual.lean').read_bytes().startswith(old.read_bytes())}
equal={b:(OUT/a).read_bytes()==(SH/b).read_bytes() for a,b in [('Color.lean','R4_ColorSelection.lean'),('Actual.lean','R4_ColorResponse.lean')]}
report={'pass':all(c['pass'] for c in checks) and all(c['pass'] for c in copies) and prefix['pass'] and all(equal.values()),
 'goalNeg2Proved':False,'round9CofinalPremiseProved':False,'actualCrossingJetDetected':False,
 'actualCouplingPremiseRefuted':False,'fullKernelConcentrationProved':False,'fullSpatialCovarianceProved':False,
 'newDeclarations':{k:len(v) for k,v in new.items()},'compilations':checks,'verbatimCopies':copies,'unchangedR3Prefix':prefix,'publicationByteEqual':equal,
 'mainDeclaration':'AdalyFormal.Round10.Dictionary.ColorResponse.vacJet_chargedPart_component',
 'obstructionDeclaration':'AdalyFormal.Round10.Dictionary.ColorObstruction.exists_charged_invisible'}
(OUT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('compilations','verbatimCopies')},indent=2))
for c in checks:print(c['path'],'exit',c['exitCode'],'records',c['recordCount'],'new',c['newDeclarationCount'],'PASS',c['pass'])
raise SystemExit(0 if report['pass'] else 1)
