#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
root = Path(__file__).resolve().parents[4]
work = root/'AHP/round13/positivity/r1'
shared = root/'AHP/round13/shared/positivity'
allowed = {'propext','Classical.choice','Quot.sound'}
records = []
for stem in ('MassAbsorption','EightLeaves','LocalPositive'):
    local = work/f'{stem}.lean'
    pub = shared/f'R1_{stem}.lean'
    assert local.read_bytes()==pub.read_bytes(), stem
    for source in (local,pub):
        data = source.read_text()
        log = Path(str(source)+'.log').read_text()
        assert Path(str(source)+'.exit').read_text().strip()=='0', source
        assert ': error:' not in log and 'error(' not in log and 'sorryAx' not in log, source
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',data), source
        axioms = []
        for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.S):
            deps = [s.strip() for s in (m.group(2) or '').split(',') if s.strip()]
            assert set(deps)<=allowed, (source,m.group(1),deps)
            axioms.append({'name':m.group(1),'axioms':deps,'logLine':1+log[:m.start()].count('\n')})
        assert axioms
        records.append({'source':str(source.relative_to(root)), 'lines':len(data.splitlines()),
            'exit':0,'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'logSha256':hashlib.sha256(log.encode()).hexdigest(),
            'records':axioms,
            'newPrintedDeclarations':sum(a['name'].startswith('AdalyFormal.Round13.Positivity') for a in axioms)})
copy_checks = []
for row in json.loads((work/'COPIES.json').read_text()):
    chunk = ''.join((root/row['source']).read_text().splitlines(keepends=True)[row['firstLine']-1:row['lastLine']])
    if 'removedUnusedOpen' in row: chunk = chunk.replace(row['removedUnusedOpen'],'')
    assert hashlib.sha256(chunk.encode()).hexdigest()==row['sha256'], row
    assert chunk in (work/row['target']).read_text(), row
    copy_checks.append({**row,'verbatim':True})
result={'status':'PASS','P2':'OPEN','verification':'builder/local and separate shared execution; not independent review',
        'compilations':records,'copyChecks':copy_checks,'newPrintedDeclarations':sum(r['newPrintedDeclarations'] for r in records[::2])}
(work/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('compilations','copyChecks')}))
