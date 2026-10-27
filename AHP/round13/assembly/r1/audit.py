#!/usr/bin/env python3
"""Read-only certificate/copy audit; never compiles or changes earlier rounds."""
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parents[4]; HERE=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def audit(path):
    p=ROOT/path; source=p.read_text(); log=Path(str(p)+'.log'); exitfile=Path(str(p)+'.exit')
    assert exitfile.read_text().strip()=='0',path
    raw=log.read_text()
    assert not re.search(r'\berror(?:\(|:)',raw),path
    entries=[]
    for m in re.finditer(r"'([^\n]+)' depends on axioms:\s*\[([^]]*)\]|'([^\n]+)' does not depend on any axioms",raw):
        name=m.group(1) or m.group(3)
        axioms=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
        assert set(axioms)<=allowed,(path,name,axioms)
        entries.append(dict(name=name,axioms=axioms,line=raw[:m.start()].count('\n')+1,literal=' '.join(m.group(0).split())))
    assert entries,path
    assert len(entries)==raw.count('depends on axioms:')+raw.count('does not depend on any axioms'),path
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source)
    assert not forbidden,(path,forbidden)
    imports=re.findall(r'^import (.+)$',source,re.M)
    assert all((ROOT/'lean/src'/f'{i}.lean').is_file() for i in imports),(path,imports)
    return dict(path=path,lines=len(source.splitlines()),source_sha256=sha(p),log_sha256=sha(log),exit=0,imports=imports,printed_axiom_records=len(entries),records=entries)
paths=['AHP/round13/assembly/r1/RepairedJoin.lean','AHP/round13/assembly/r1/Spine.lean','AHP/round13/assembly/r1/StartedSpine.lean','AHP/round13/shared/assembly/R1_Spine.lean','AHP/round13/assembly/r1/P1Spine.lean','AHP/round13/shared/assembly/R1_P1Spine.lean']
results=[audit(p) for p in paths]
assert (HERE/'StartedSpine.lean').read_bytes()==(ROOT/'AHP/round13/shared/assembly/R1_Spine.lean').read_bytes()
assert (HERE/'P1Spine.lean').read_bytes()==(ROOT/paths[-1]).read_bytes()
copies=[]
for name,target in [('SPINE_COPIES.json',HERE/'Spine.lean'),('START_COPIES.json',HERE/'StartedSpine.lean'),('P1_COPIES.json',HERE/'P1Spine.lean')]:
    for r in json.loads((HERE/name).read_text()):
        data=''.join((ROOT/r['path']).read_text().splitlines(keepends=True)[r['start_line']-1:r['end_line']])
        assert hashlib.sha256(data.encode()).hexdigest()==r['sha256'],r
        assert data in target.read_text(),r
        copies.append(r)
repair=json.loads((HERE/'REPAIR_COPIES.json').read_text())
assert sha(ROOT/repair['original'])==repair['original_sha256']
assert sha(HERE/'RepairedJoin.lean')==repair['output_sha256']
for r in repair['helpers']:
    data=''.join((ROOT/r['source']).read_text().splitlines(keepends=True)[r['start_line']-1:r['end_line_exclusive']-1])
    assert hashlib.sha256(data.encode()).hexdigest()==r['sha256'],r
    assert data in (HERE/'RepairedJoin.lean').read_text(),r
# Check the pinned target and each original interface crossing the two certificates.
def declaration(p,name):
    source=p.read_text()
    m=re.search(r'^(?:noncomputable )?(?:def|abbrev) '+re.escape(name)+r'\b',source,re.M)
    assert m,(p,name)
    return source[m.start():source.index('\n\n',m.start())].strip()
interfaces=[]
for name in ['vacA','vacEdge','KernelLine','NoResponseCancellation','CofinalAnyPathCurlLine','CofinalAnyPathNoResponseCancellation']:
    a=declaration(HERE/'RepairedJoin.lean',name)
    b=declaration(HERE/'StartedSpine.lean',name)
    assert a==b,name
    interfaces.append(dict(name=name,sha256=hashlib.sha256(a.encode()).hexdigest(),verbatim=True))
pin=ROOT/'AHP/round3/guarded/pin/Statement.lean'
for name in ['CoercG8AtSG','P428Target8SG','GoalPos2','GoalNeg2']:
    a=declaration(pin,name); b=declaration(HERE/'RepairedJoin.lean',name)
    assert a==b,name
    interfaces.append(dict(name=name,sha256=hashlib.sha256(a.encode()).hexdigest(),pinned_verbatim=True))
# Independently inspect currently published sibling source/log/exit triples.
siblings=[]
for p in sorted((ROOT/'AHP/round13/shared').glob('*/*.lean')):
    if p.parent.name=='assembly': continue
    if Path(str(p)+'.exit').is_file() and Path(str(p)+'.exit').read_text().strip()=='0':
        siblings.append(audit(str(p.relative_to(ROOT))))
report=dict(status='PASS',goal_status='OPEN: P1 proved and integrated; P2/P3 and GoalNeg2 remain open',compiles=results,
    verbatim_source_ranges=copies,repair=repair,shared_copy_identical=True,interfaces=interfaces,
    sibling_certificates_inspected=siblings,
    terminal=dict(id='term_i4rxw7r37d',scope='environment env_5s9d5u8vgk',repair_compilations=1,exit=0,
      initial_thread_terminal_create='HTTP 409 before process launch; no compilation occurred',
      command='bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r1/RepairedJoin.lean'))
(HERE/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(results),'own clean compiles;',len(copies),'verbatim ranges;',len(siblings),'sibling certificates')
for r in results: print(r['path'],r['printed_axiom_records'],'standard axiom records')
