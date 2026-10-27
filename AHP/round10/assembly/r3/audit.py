#!/usr/bin/env python3
"""Audit ONLY successful artifacts. Historical failure logs are explicitly excluded."""
from pathlib import Path
import re,json,hashlib
P=Path(__file__).resolve().parent;ROOT=P.parents[3]
S=ROOT/'AHP/round10/shared/assembly';allowed={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[P/'Neutral.lean',P/'Compact.lean',P/'JetCompact.lean',S/'R3_NeutralResponse.lean',S/'R3_EnergyGlue.lean',S/'R3_JetGlue.lean']
result={'compiled':[]}
for p in files:
 log=Path(str(p)+'.log');ex=Path(str(p)+'.exit');txt=log.read_text()
 assert ex.read_text().strip()=='0',(p,'exit')
 assert log.stat().st_mtime>=p.stat().st_mtime,(p,'stale log')
 assert not re.search(r'error(?:\(|:)|sorryAx|declaration uses',txt),(p,'diagnostic')
 records=[]
 for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",txt,re.S):
  ax=set(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
  assert ax<=allowed,(p,m.group(1),ax)
  records.append({'name':m.group(1),'axioms':sorted(ax)})
 assert records,p
 assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^axiom\s',p.read_text(),re.M),p
 result['compiled'].append({'file':str(p.relative_to(ROOT)),'lines':len(p.read_text().splitlines()),'sha256':sha(p),'log_sha256':sha(log),'exit':0,'records':records})
for a,b in [('Neutral.lean','R3_NeutralResponse.lean'),('Compact.lean','R3_EnergyGlue.lean'),('JetCompact.lean','R3_JetGlue.lean')]:
 assert (P/a).read_bytes()==(S/b).read_bytes()
r9=ROOT/'AHP/round9/qualitative-r2/Attempt.lean';r2=ROOT/'AHP/round10/assembly/r2/Attempt.lean';attempt=P/'Attempt.lean'
assert attempt.read_bytes().startswith(r9.read_bytes())
assert attempt.read_bytes().startswith(r2.read_bytes())
assert not Path(str(attempt)+'.exit').exists(),'Historical file must not be reported compiled'
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^axiom\s',attempt.read_text(),re.M)
result['historical']={'file':str(attempt.relative_to(ROOT)),'sha256':sha(attempt),'lines':len(attempt.read_text().splitlines()),'round9_prefix_bytes':len(r9.read_bytes()),'round9_sha256':sha(r9),'round9_prefix_exact':True,'round2_assembly_prefix_exact':True,'compiled':False,'reason':'Coordinator prohibits large compilation on 16GB worker; final regularity/flat-unit/GoalNeg2 applications remain uncompiled.'}
# Confirm all small operative copies appear verbatim in their declared source.
for c in json.loads((P/'COPIES.json').read_text()):
 src=(ROOT/c['source']).read_text();m=re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev|lemma) '+re.escape(c['name'])+r'\b',src,re.M);assert m,c
 n=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |lemma |open |end |namespace |section|variable |include |omit |#print |/[-!])',src[m.end():])
 end=m.end()+n.start()+1 if n else len(src);body=src[m.start():end].rstrip()+'\n'
 assert hashlib.sha256(body.encode()).hexdigest()==c['sha256'],c
result['operative_copies']=len(json.loads((P/'COPIES.json').read_text()))
result['new_assembly_declarations']=[r for r in result['compiled'][2]['records'] if r['name'].startswith('AdalyFormal.Round10.Assembly.R3.')]
result['goal_proved']=False
result['remaining']=['nonzero actual crossing jet/curl','whole-kernel containment or another common-sign argument','nested cofinal scales/radii','compile historical regularity/unit/final bridge join']
(P/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(files),'successful files,',len(result['new_assembly_declarations']),'new R3 declarations; GoalNeg2 OPEN; historical join NOT COMPILED')
for f in result['compiled']:print(f['file'],f['lines'],'lines',len(f['records']),'axiom records')
