from pathlib import Path
import re,json,hashlib,subprocess,ast
D=Path('AHP/round4/guarded/mine');root=D.parent
pin=Path('AHP/round3/guarded/pin/Statement.lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (root/'Attempt.lean').read_bytes()==pin.read_bytes()
allowed={'propext','Classical.choice','Quot.sound'}
pat=re.compile(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",re.M)
forbidden=re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b')
files=[root/'Attempt.lean',D/'Trace.lean',D/'ChecksV2.lean',D/'ChecksV3.lean',D/'ChecksExtra.lean']
summary={'pin':str(pin),'pinSha256':sha(pin),'attemptMatchesPin':True,'newMathematicalResults':False,'compiledFiles':[]}
for p in files:
 log=Path(str(p)+'.log');ex=Path(str(p)+'.exit')
 assert ex.read_text().strip()=='0',p
 txt=p.read_text();lt=log.read_text()
 assert not re.search(r'error:|warning:',lt),p
 assert not forbidden.search(txt),p
 assert p.stat().st_mtime<=log.stat().st_mtime<=ex.stat().st_mtime,p
 imports=re.findall(r'^import\s+(\S+)',txt,re.M)
 assert all((Path('lean/src')/(m.replace('.','/')+'.lean')).is_file() for m in imports),(p,imports)
 records=[]
 for m in pat.finditer(lt):
  axs={x.strip() for x in (m[2] or '').split(',') if x.strip()};assert axs<=allowed,(p,m[1],axs);records.append(m[1])
 requested=re.findall(r'^#print axioms (.+)$',txt,re.M)
 assert len(records)==len(requested) and all(any(n==q or n.endswith('.'+q) for n in records) for q in requested),(p,len(records),len(requested))
 summary['compiledFiles'].append({'file':str(p),'sha256':sha(p),'exit':0,'axiomRecords':len(records),'imports':imports,'diagnostics':[]})
manifest=json.loads((D/'manifest.json').read_text());catalog=json.loads((D/'catalog.json').read_text())
assert len(manifest)==len(catalog)==419
assert {d['name'] for d in manifest}=={d['name'] for d in catalog}
origins={};audited=[]
for p in [D/'ChecksV3.lean',D/'ChecksExtra.lean']:
 audited+=re.findall(r'^#check (.+)$',p.read_text(),re.M)
 for m in re.finditer(r'^ORIGIN\|([^|]+)\|(.+)$',Path(str(p)+'.log').read_text(),re.M):origins[m[1]]=m[2]
assert set(audited)=={d['name'] for d in catalog} and len(audited)==419
for d in catalog:
 assert origins[d['name']]==Path(d['file']).stem
 assert d['sourceStatement'] in Path(d['file']).read_text(),d['name']
 assert d['type'].startswith(d['name']),d['name']
 if d['kind'] in ('theorem','lemma'):
  # Source extraction must not stop at a named/default argument or record update.
  for a,b in [('(',')'),('[',']'),('{','}')]:assert d['sourceStatement'].count(a)==d['sourceStatement'].count(b),(d['name'],a)
 assert set(d['axioms'])<=allowed
report=(root/'MINE.md').read_text()
assert report.count('<details>')==419 and report.count('</details>')==419
assert report.count('**Constant order:**')==419 and report.count('**Selector:**')==419
for d in catalog:assert d['axiomLine'] in report and f'{d["file"]}:{d["line"]}' in report
for p in D.glob('*.py'):ast.parse(p.read_text())
summary.update({'declarations':len(catalog),'allSourceModulesMatch':True,'allSourceSignaturesBalanced':True,'allPermittedAxioms':True,'traceConstantCount':sum(1 for s in (D/'Trace.lean.log').read_text().splitlines() if s.startswith('DEPENDENCY|')),'report':str(root/'MINE.md'),'reportSha256':sha(root/'MINE.md'),'trackedDiffPaths':subprocess.check_output(['git','diff','--name-only'],text=True).splitlines(),'scope':'Mining only; pinned guarded goals remain open. Existing unrelated lakefile/Compact work was not edited.'})
assert not Path('AHP/round4-search.tmp').exists()
(D/'VERIFY.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False,indent=2))
