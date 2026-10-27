#!/usr/bin/env python3
"""Audit compiled dictionary R3 artifacts. This script proves no mathematics."""
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parents[4]
OUT=ROOT/'AHP/round10/dictionary/r3'
SHARED=ROOT/'AHP/round10/shared/dictionary'
allowed={'propext','Classical.choice','Quot.sound'}
files=[OUT/'Scalar.lean',OUT/'Actual.lean',OUT/'JetDetection.lean',
       SHARED/'R3_FreeSource.lean',SHARED/'R3_JetDetection.lean']
new={}
for file,ns in [('ScalarAppendix.lean','SourceEnergy'),('ActualAppendix.lean','FreeSource'),('JetAppendix.lean','JetDetection')]:
    new[ns]=['AdalyFormal.Round10.Dictionary.'+ns+'.'+m.group(1) for m in
        re.finditer(r'^(?:theorem|lemma|def|abbrev)\s+(\w+)',(OUT/file).read_text(),re.M)]
checks=[]
for f in files:
    s=f.read_text(); log=Path(str(f)+'.log'); ex=Path(str(f)+'.exit'); t=log.read_text()
    axioms={m.group(1):set(x.strip() for x in (m.group(2) or '').split(',') if x.strip()) for m in
        re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",t)}
    groups=['SourceEnergy']
    if 'Scalar' not in f.name: groups.append('FreeSource')
    if 'JetDetection' in f.name: groups.append('JetDetection')
    expected=[d for g in groups for d in new[g]]
    c={'path':str(f.relative_to(ROOT)),'lines':len(s.splitlines()),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
       'exit':ex.read_text().strip(),'fresh':f.stat().st_mtime <= log.stat().st_mtime <= ex.stat().st_mtime,
       'imports':re.findall(r'^import (.*)$',s,re.M),'diagnostics':re.findall(r'^.*(?:error:|warning:|sorryAx).*$' ,t,re.M),
       'forbiddenSourceTokens':re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s),
       'records':len(axioms),'newDeclarations':len(expected),'missingPrints':[d for d in expected if d not in axioms],
       'nonstandard':{k:sorted(v-allowed) for k,v in axioms.items() if not v<=allowed}}
    c['pass']=c['exit']=='0' and c['fresh'] and not any(c[k] for k in ['diagnostics','forbiddenSourceTokens','missingPrints','nonstandard'])
    c['pass']=c['pass'] and c['imports']==(['DrEquiv','ZXR2Flat6'] if 'JetDetection' in f.name else ['DrEquiv'])
    checks.append(c)
pairs=[('Actual.lean','R3_FreeSource.lean'),('JetDetection.lean','R3_JetDetection.lean')]
publication={b:(OUT/a).read_bytes()==(SHARED/b).read_bytes() for a,b in pairs}
copychecks=[]
for rec in json.loads((OUT/'COPIES.json').read_text()):
    src=(ROOT/rec['source']).read_text()
    if 'fragment' in rec:
        frag=rec['fragment']; ok=frag in src and hashlib.sha256(frag.encode()).hexdigest()==rec['sha256']
        ok=ok and frag in (OUT/'Scalar.lean').read_text()
    else:
        ok=hashlib.sha256(src.encode()).hexdigest()==rec['sha256']
        if rec.get('wholeFile'):
            ok=ok and (OUT/'Actual.lean').read_text().startswith(src)
        else:
            reduced=src.replace(rec['omitted'],'',1)
            reduced='\n'.join(l for l in reduced.splitlines() if not l.startswith('import '))+'\n'
            ok=ok and reduced in (OUT/'JetDetection.lean').read_text()
    copychecks.append({'source':rec['source'],'pass':ok})
report={'pass':all(c['pass'] for c in checks) and all(publication.values()) and all(c['pass'] for c in copychecks),
    'goalNeg2Proved':False,'round9CofinalPremiseProved':False,'crossingTopJetNonzeroProved':False,
    'fullKernelConcentrationProved':False,'newDeclarations':{k:len(v) for k,v in new.items()},
    'compilations':checks,'publicationByteEqual':publication,'verbatimCopyChecks':copychecks,
    'mainDeclaration':'AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet'}
(OUT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
raise SystemExit(0 if report['pass'] else 1)
