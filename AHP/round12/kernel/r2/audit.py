#!/usr/bin/env python3
"""Copy/compile/artifact audit, not an independent proof checker."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[3]
allowed={'propext','Classical.choice','Quot.sound'}
paths=[H/n for n in ('BoundaryDressing.lean','LineResponse.lean','ActualResponse.lean','ActualCrossing.lean')]
paths += [ROOT/'AHP/round12/shared/kernel'/n for n in ('R2_ResponseLine.lean','R2_FirstCrossing.lean')]
reports=[]
for p in paths:
    src=p.read_text();lp=p.with_suffix('.lean.log');ep=p.with_suffix('.lean.exit');log=lp.read_text()
    records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
    used={a.strip() for _,r in records for a in r.split(',') if a.strip()}
    bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',src)
    diag=re.findall(r'^.*(?:error:|sorryAx).*$',log,re.M)
    imports=re.findall(r'^import (.*)$',src,re.M)
    rec={'path':str(p.relative_to(ROOT)),'lines':len(src.splitlines()),'imports':imports,
      'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'log_sha256':hashlib.sha256(lp.read_bytes()).hexdigest(),
      'exit':int(ep.read_text().strip()),'axioms':sorted(used),'axiom_count':len(records),
      'records':[{'name':n,'axioms':[a.strip() for a in r.split(',') if a.strip()]} for n,r in records],
      'forbidden_tokens':bad,'errors':diag,'fresh':p.stat().st_mtime<=lp.stat().st_mtime<=ep.stat().st_mtime}
    rec['pass']=rec['exit']==0 and rec['fresh'] and not bad and not diag and bool(records) and used<=allowed and imports==['DrEquiv']
    reports.append(rec)
actual=(H/'ActualResponse.lean').read_text();copies=[]
for r in json.loads((H/'COPIES.json').read_text()):
    src=(ROOT/r['path']).read_text()
    if not r.get('entire_file'):
        a=src.index(r['start']);b=src.index(r['end'],a);src=src[a:b]
    copies.append({'source':r['path'],'hash_matches':hashlib.sha256(src.encode()).hexdigest()==r['sha256'],
      'present_verbatim':src in actual})
cross=(H/'ActualCrossing.lean').read_text();cc=json.loads((H/'CROSSING_COPIES.json').read_text())
for key in ('prefix','helpers'):
    r=cc[key];src=(ROOT/r['path']).read_text()
    if key=='helpers':src=''.join(src.splitlines(keepends=True)[r['start_line']-1:r['end_line']-1])
    copies.append({'source':r['path'],'part':key,'hash_matches':hashlib.sha256(src.encode()).hexdigest()==r['sha256'],
      'present_verbatim':src in cross})
identical={a:(H/a).read_bytes()==(ROOT/'AHP/round12/shared/kernel'/b).read_bytes()
    for a,b in [('ActualResponse.lean','R2_ResponseLine.lean'),('ActualCrossing.lean','R2_FirstCrossing.lean')]}
result={'compiles':reports,'copies':copies,'shared_byte_identical':identical,
  'new_generic_response_body_verbatim':(H/'LineResponse.lean').read_text().removeprefix('import DrEquiv\n') in actual,
  'qualification':'Only conditional geometric implications and actual response identities; no cofinal premise or GoalNeg2 proof.'}
result['pass']=all(r['pass'] for r in reports) and all(r['hash_matches'] and r['present_verbatim'] for r in copies) and all(identical.values()) and result['new_generic_response_body_verbatim']
(H/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':result['pass'],'files':[{k:r[k] for k in ('path','lines','exit','axiom_count','pass')} for r in reports],
 'copies':len(copies),'identical':identical},indent=2))
raise SystemExit(0 if result['pass'] else 1)
