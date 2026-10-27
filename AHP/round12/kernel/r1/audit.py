#!/usr/bin/env python3
"""Artifact/copy/axiom audit; it is not a mathematical proof checker."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
ALLOWED={'propext','Classical.choice','Quot.sound'}
reports=[]
for p in [HERE/'KernelStructure.lean',HERE/'ActualKernel.lean',ROOT/'AHP/round12/shared/kernel/R1_ActualKernel.lean']:
    src=p.read_text();log=p.with_suffix('.lean.log');ex=p.with_suffix('.lean.exit')
    text=log.read_text()
    records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
    axioms={a.strip() for _,r in records for a in r.split(',') if a.strip()}
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',src)
    # Every newly introduced namespace declaration has an explicit record.
    new=[name for name,_ in records if name.startswith('AdalyFormal.Round12.Kernel.')]
    imports=re.findall(r'^import (.*)$',src,re.M)
    report={'file':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'lines':len(src.splitlines()),'imports':imports,'exit':ex.read_text().strip(),
      'axiom_records':len(records),'axioms':sorted(axioms),'new_records':new,
      'forbidden_tokens':forbidden,'errors':re.findall(r'^.*(?:error:|sorryAx).*$',text,re.M),
      'fresh':p.stat().st_mtime<=log.stat().st_mtime<=ex.stat().st_mtime}
    report['pass']=(report['exit']=='0' and report['fresh'] and not forbidden and not report['errors']
      and axioms<=ALLOWED and len(records)>0 and imports==(['D1IVT'] if p.name=='KernelStructure.lean' else ['DrEquiv']))
    reports.append(report)
base=ROOT/'AHP/round10/shared/dictionary/R1_Dictionary.lean'
actual=(HERE/'ActualKernel.lean').read_text()
core=(HERE/'KernelStructure.lean').read_text().split('namespace AdalyFormal.Round12.Kernel',1)[1]
core='namespace AdalyFormal.Round12.Kernel'+core
copies=[]
for item in json.loads((HERE/'COPIES.json').read_text()):
    p=ROOT/item['path'];text=p.read_text()
    if not item.get('entire_file'):
        text=''.join(text.splitlines(keepends=True)[item['start_line']-1:item['end_line_exclusive']-1])
    copies.append({'source':item['path'],
      'hash_matches':hashlib.sha256(text.encode()).hexdigest()==item['sha256'],
      'present_verbatim':text in actual})
result={'files':reports,'copy_checks':copies,
 'dictionary_prefix_verbatim':actual.startswith(base.read_text()),
 'generic_body_verbatim':core in actual,
 'shared_byte_identical':(HERE/'ActualKernel.lean').read_bytes()==(ROOT/'AHP/round12/shared/kernel/R1_ActualKernel.lean').read_bytes()}
result['pass']=all(r['pass'] for r in reports) and all(x['present_verbatim'] and x['hash_matches'] for x in copies) and all(result[k] for k in ['dictionary_prefix_verbatim','generic_body_verbatim','shared_byte_identical'])
(HERE/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['pass'] else 1)
