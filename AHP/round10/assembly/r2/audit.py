#!/usr/bin/env python3
"""Artifact audit. Passing this audit does not prove a cofinal premise."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
fail=[]
def require(test,message):
    if not test: fail.append(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def audit_lean(p,imp,newprefix):
    s=p.read_text(); log=p.with_suffix(p.suffix+'.log'); ex=p.with_suffix(p.suffix+'.exit')
    require(ex.exists() and ex.read_text().strip()=='0',f'{p}: exit')
    require(re.findall(r'^import (.+)$',s,re.M)==[imp],f'{p}: imports')
    require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',s),f'{p}: prohibited token')
    t=log.read_text()
    require(not re.search(r'error:|warning:|sorryAx',t),f'{p}: diagnostics')
    require(p.stat().st_mtime<=log.stat().st_mtime<=ex.stat().st_mtime,f'{p}: timestamps')
    records=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",t,re.S)
    require(bool(records),f'{p}: no records')
    for name,ds in records:
        deps={d.strip() for d in ds.split(',') if d.strip()}
        require(deps<=ALLOWED,f'{p}: {name}: {deps}')
    own=[n for n,_ in records if n.startswith(newprefix)]
    return dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes()),lines=len(s.splitlines()),exit=ex.read_text().strip(),records=len(records),new_records=own)
rows=[audit_lean(HERE/'Compact.lean','DrEquiv','AdalyFormal.Round10.Assembly.R2.'),
      audit_lean(ROOT/'AHP/round10/shared/assembly/R2_SourceGlue.lean','DrEquiv','AdalyFormal.Round10.Assembly.R2.'),
      audit_lean(HERE/'ProfileQuantifiers.lean','D1IVT','AdalyFormal.Round10.Assembly.ProfileQuantifiers.'),
      audit_lean(ROOT/'AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean','D1IVT','AdalyFormal.Round10.Assembly.ProfileQuantifiers.')]
require(rows[0]['sha256']==rows[1]['sha256'],'compact/shared equality')
require(rows[2]['sha256']==rows[3]['sha256'],'quantifiers/shared equality')
for file,index in [('Appendix.lean',0),('ProfileQuantifiers.lean',2)]:
    names=re.findall(r'^(?:(?:noncomputable )?def|theorem|lemma) (\w+)\b',(HERE/file).read_text(),re.M)
    printed={n.rsplit('.',1)[-1] for n in rows[index]['new_records']}
    require(set(names)<=printed,f'{file}: missing individual axiom record {set(names)-printed}')
compact=(HERE/'Compact.lean').read_text()
manifest=json.loads((HERE/'COPIES.json').read_text())
dictionary=(HERE/'DictionaryAppendix.lean').read_text()
halfmanifest=json.loads((HERE/'DICTIONARY_APPENDIX_COPIES.json').read_text())
for m,target in [(m,compact) for m in manifest]+[(m,dictionary) for m in halfmanifest]:
    src=(ROOT/m['source']).read_text()
    start=sum(len(x) for x in src.splitlines(keepends=True)[:m['line']-1])
    # The exact slice is specified by declaration start and next top-level boundary.
    match=re.match(r'(?:(?:noncomputable )?def|theorem|abbrev|lemma) '+re.escape(m['name'])+r'\b',src[start:])
    require(bool(match),f'copy start {m}')
    e0=start+match.end()
    nxt=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |lemma |open |end |namespace |#print |/[-!])',src[e0:])
    end=e0+nxt.start()+1 if nxt else len(src)
    block=src[start:end].rstrip()+'\n'
    require(sha(block.encode())==m['sha256'],f'copy hash {m["name"]}')
    require(block in target,f'copy missing {m["name"]}')
inc=[]
for rel in ['AHP/round10/shared/nonvanishing/R1_SourceDominance.lean','AHP/round10/shared/nonvanishing/R2_SourceFamily.lean','AHP/round10/shared/assembly/R1_Cofinal.lean']:
    raw=(ROOT/rel).read_text(); body=raw.removeprefix('import D1IVT\n')
    require(body in compact,f'full body not included {rel}')
    inc.append(dict(path=rel,sha256=sha(raw.encode())))
r9=ROOT/'AHP/round9/qualitative-r2/Attempt.lean'
full=HERE/'Attempt.lean'
require(full.read_bytes().startswith(r9.read_bytes()),'round9 verbatim prefix')
require(not full.with_suffix('.lean.exit').exists(),'unexpected large compilation record')
require(dictionary in full.read_text(),'dictionary appendix not in Attempt')
for f in ['PhaseSource.lean','KKT.lean','SourceAppendix.lean']:
    require((ROOT/'AHP/round10/dictionary/r2'/f).read_text().removeprefix('import DrEquiv\n') in dictionary,f'dictionary fragment missing {f}')
dr=json.loads((HERE/'DICTIONARY_REVIEW.json').read_text())
require(dr['pass'] and dr['sha256']==sha((ROOT/dr['path']).read_bytes()),'dictionary publication review not current')
nums=[]
for p in sorted((HERE/'numerics').glob('*.json')):
    if p.stem=='SUMMARY': continue
    ex=p.with_suffix('.exit')
    require(ex.exists() and ex.read_text().strip()=='0',f'numeric exit {p}')
    nums.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes())))
report=dict(pass_=not fail,failures=fail,goalNeg2_proved=False,round9_premise_proved=False,
    actual_source_dictionary_proved=False,actual_crossing_jet_proved=False,full_kernel_line_proved=False,
    concrete_conditional_glue_compiled=True,full_attempt_compiled=False,
    compiled=rows,copied_declarations=len(manifest),shared_bodies=inc,
    dictionary_half_rotation_copies=len(halfmanifest),reviewed_dictionary=dr,
    dictionary_appendix_sha256=sha(dictionary.encode()),
    round9_prefix_bytes=len(r9.read_bytes()),round9_sha256=sha(r9.read_bytes()),
    full_attempt_lines=len(full.read_text().splitlines()),full_attempt_sha256=sha(full.read_bytes()),numerics=nums)
report['pass']=report.pop('pass_')
(HERE/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS' if not fail else 'FAIL',f'{len(rows[0]["new_records"])} concrete declarations, {len(rows[2]["new_records"])} quantifier declarations')
for x in fail: print(x)
raise SystemExit(bool(fail))
