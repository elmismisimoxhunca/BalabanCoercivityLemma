#!/usr/bin/env python3
"""Read/audit all current shared artifacts; never claim uncompiled goals proved."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
ROOT=P.parents[3]
S=ROOT/'AHP/round10/shared'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p): return str(p.relative_to(ROOT))
def records(text):
 out=[]
 for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text,re.S):
  ax=sorted(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
  assert set(ax)<=ALLOWED,(m.group(1),ax)
  out.append({'name':m.group(1),'axioms':ax})
 return out
def audit_lean(p):
 source=p.read_text(); log=Path(str(p)+'.log'); ex=Path(str(p)+'.exit')
 text=log.read_text()
 assert ex.read_text().strip()=='0',(p,'exit')
 assert p.stat().st_mtime<=log.stat().st_mtime<=ex.stat().st_mtime,(p,'stale')
 assert not re.search(r'\b(?:warning|error)(?:\(|:)|sorryAx|declaration uses',text),(p,'diagnostics')
 assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b|^axiom\s',source,re.M),(p,'prohibited device')
 rr=records(text);assert rr,(p,'empty audit')
 return {'path':rel(p),'lines':len(source.splitlines()),'sha256':sha(p),'log_sha256':sha(log),'exit':0,'records':rr}
compiled=[audit_lean(p) for p in [P/'Cone.lean',P/'Compact.lean',S/'assembly/R4_ResponseHull.lean']]
assert (P/'Compact.lean').read_bytes()==(S/'assembly/R4_ResponseHull.lean').read_bytes()
base=S/'assembly/R3_EnergyGlue.lean'
assert (P/'Compact.lean').read_bytes().startswith(base.read_bytes())
old=json.loads((ROOT/'AHP/round10/assembly/r3/AUDIT.json').read_text())
base_record=next(x for x in old['compiled'] if x['file']==rel(base))
assert sha(base)==base_record['sha256']
assert sha(Path(str(base)+'.log'))==base_record['log_sha256']
# Exact operative-copy provenance carried by the unchanged R3 compact prefix.
for c in json.loads((ROOT/'AHP/round10/assembly/r3/COPIES.json').read_text()):
 src=(ROOT/c['source']).read_text()
 m=re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev|lemma) '+re.escape(c['name'])+r'\b',src,re.M);assert m,c
 n=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |lemma |open |end |namespace |section|variable |include |omit |#print |/[-!])',src[m.end():])
 end=m.end()+n.start()+1 if n else len(src)
 body=src[m.start():end].rstrip()+'\n'
 assert hashlib.sha256(body.encode()).hexdigest()==c['sha256'],c
new=[r for r in compiled[1]['records'] if r['name'].startswith('AdalyFormal.Round10.Assembly.R4.')]
expected=[]
for name in ['Cone.lean','ConeActualAppendix.lean','CofinalAppendix.lean']:
 expected += ['AdalyFormal.Round10.Assembly.R4.'+x for x in re.findall(r'^(?:theorem|def|abbrev) (\w+)',(P/name).read_text(),re.M)]
assert len(new)==len(expected)==26
assert set(expected)=={x['name'] for x in new}
# Read EVERY shared file, not only the files consumed by the new proof.
shared_files=[]
for p in sorted(S.rglob('*')):
 if p.is_file():
  body=p.read_text()
  shared_files.append({'path':rel(p),'sha256':sha(p),'bytes':p.stat().st_size,'lines':len(body.splitlines())})
shared_lean=[audit_lean(p) for p in sorted(S.rglob('*.lean'))]
notes=[]
for p in sorted((ROOT/'AHP/round10').glob('*/r*/NOTES.md')):
 body=p.read_text()
 notes.append({'path':rel(p),'sha256':sha(p),'lines':len(body.splitlines()),'work_in_progress':'work in progress' in body.lower()})
# Historical assembly is deliberately uncompiled. It must retain the entire R9 prefix.
r9=ROOT/'AHP/round9/qualitative-r2/Attempt.lean'
r3=ROOT/'AHP/round10/assembly/r3/Attempt.lean'
att=P/'Attempt.lean'
assert att.read_bytes().startswith(r9.read_bytes())
assert att.read_bytes().startswith(r3.read_bytes())
assert not Path(str(att)+'.exit').exists() and not Path(str(att)+'.log').exists()
for name in ['ConeActualAppendix.lean','CofinalAppendix.lean','GoalAppendix.lean']:
 assert (P/name).read_bytes() in att.read_bytes()
ds=(S/'dictionary/R4_ColorResponse.lean').read_bytes()
ci=ds.index(b'namespace AdalyFormal.Round10.Dictionary.Color\n')
gi=ds.index(b'namespace AdalyFormal.Round4.Guarded.RefuteR1\n',ci)
oi=ds.index(b'namespace AdalyFormal.Round10.Dictionary.ColorObstruction\n',gi)
assert ds[ci:gi] in att.read_bytes() and ds[oi:] in att.read_bytes()
poly=(S/'nonvanishing/R4_PolynomialCertificate.lean').read_bytes().replace(b'import D1IVT\n',b'',1)
assert poly in att.read_bytes()
summary=json.loads((P/'numerics/SUMMARY.json').read_text())
assert summary['precisions']==[180,230,240]
result={'pass':True,'compiled':compiled,'new_assembly_declarations':new,
 'shared_review':{'files':shared_files,'compiled_files':shared_lean,'notes':notes,
 'qualification':'Shared logs inspected, not all independently recompiled by assembly R4. Original R4 track notes may be work-in-progress; source/log/exit evidence is audited directly.'},
 'historical':{'file':rel(att),'lines':len(att.read_text().splitlines()),'sha256':sha(att),'r9_sha256':sha(r9),'r9_prefix_bytes':r9.stat().st_size,'r9_prefix_exact':True,'r3_prefix_exact':True,'r4_cross_track_bodies_exact':True,'compiled':False,'reason':'Coordinator forbids 12k+ historical compilation on this memory-limited worker; regularity/final goal joins not verified.'},
 'numerics_summary_sha256':sha(P/'numerics/SUMMARY.json'),
 'goalNeg2_proved':False,'round9_premise_proved':False,'cofinalNoResponseCancellation_proved':False,
 'remaining':['Prove actual response noncancellation on complete crossing kernels at nested cofinal scales/radii; equivalently original free-profile premise.', 'Alternatively genuine crossing CurlDetected/TopJetDetected plus KernelLine at nested cofinal instances.', 'Compile the explicitly deferred historical regularity/unit/final goal join.']}
(P/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 3 successful local/shared R4 files, 26 new declarations, standard axioms only.')
print('Shared audit:',len(shared_files),'files;',len(shared_lean),'compiled Lean publications;',len(notes),'notes.')
print('Historical:',result['historical']['lines'],'lines; NOT compiled. GoalNeg2 OPEN.')
for x in compiled: print(x['path'],x['lines'],'lines',len(x['records']),'records')
