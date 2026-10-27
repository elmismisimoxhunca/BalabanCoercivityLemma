#!/usr/bin/env python3
"""Artifact/source audit only. It does not prove the missing spectral premise."""
from pathlib import Path
import re, json, hashlib
root = Path(__file__).resolve().parent
repo = root.parents[3]
shared = repo / 'AHP/round10/shared/dictionary/R1_Dictionary.lean'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
files = [root/f'{n}.lean' for n in ('Core','Gauge','Translation','Actual')] + [shared]
rows = []
for p in files:
    source = p.read_text()
    logp = Path(str(p)+'.log')
    exitp = Path(str(p)+'.exit')
    log = logp.read_text()
    records = {name: set(a.strip() for a in ax.split(',') if a.strip())
               for name, ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)}
    row = dict(file=str(p.relative_to(repo)),sha256=hashlib.sha256(source.encode()).hexdigest(),
               lines=len(source.splitlines()),exit=exitp.read_text().strip(),
               records=len(records),axioms_ok=bool(records) and all(a<=allowed for a in records.values()),
               no_errors=not re.search(r'\berror(?:\(|:)|sorryAx',log),
               no_warnings='warning:' not in log,
               chronology=p.stat().st_mtime<=logp.stat().st_mtime<=exitp.stat().st_mtime,
               imports=re.findall(r'^import (.+)$',source,re.M),
               no_forbidden=not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source))
    row['pass'] = row['exit']=='0' and row['imports']==['DrEquiv'] and all(row[k] for k in
                       ('axioms_ok','no_errors','no_warnings','chronology','no_forbidden'))
    rows.append(row)
# Every declaration authored in this round's own namespaces has a printed record.
expected=[]
for name, prefix in [('Core',''),('U1Appendix',''),('Translation','Translation.'),('ActualAppendix','Actual.')]:
    text=(root/f'{name}.lean').read_text()
    expected += ['AdalyFormal.Round10.Dictionary.'+prefix+n for n in
                 re.findall(r'^(?:@\[simp\] )?(?:(?:noncomputable )?def|theorem|abbrev) (\w+)',text,re.M)]
log=(root/'Actual.lean.log').read_text()
found=set(re.findall(r"'([^']+)' depends on axioms:",log))
missing=sorted(set(expected)-found)
# Check copied declaration bytes against both their earlier source and final harness.
copies=json.loads((root/'COPIES.json').read_text())
actual=(root/'Actual.lean').read_text()
copy_checks=[]
for c in copies:
    src=(repo/c['source']).read_text()
    m=re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev) '+re.escape(c['name'])+r'\b',src,re.M)
    nxt=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |open |end |namespace |#print |/[-!])',src[m.end():])
    e=m.end()+nxt.start()+1 if nxt else len(src)
    val=src[m.start():e].rstrip()+'\n'
    copy_checks.append(hashlib.sha256(val.encode()).hexdigest()==c['sha256'] and val in actual)
result=dict(status='partial_dictionary_only_GoalNeg2_open',files=rows,
            own_declarations=len(set(expected)),missing_axiom_records=missing,
            verbatim_copies=len(copy_checks),all_verbatim=all(copy_checks),
            shared_byte_identical=shared.read_bytes()==(root/'Actual.lean').read_bytes(),
            large_historical_attempt='killed_by_host_8GiB_command_memory_cap_no_exit_not_a_success')
result['pass']=all(r['pass'] for r in rows) and not missing and all(copy_checks) and result['shared_byte_identical']
(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['pass'] else 1)
