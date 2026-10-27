#!/usr/bin/env python3
"""Small artifact audit; no Lean invocation and no claim of research closure."""
from pathlib import Path
import hashlib
import json
import re

base=Path(__file__).resolve().parent
root=base.parents[3]
source=(base/'Attempt.lean').read_text()
log=(base/'Attempt.lean.log').read_text()
pin=(base.parent/'pin/Statement.lean').read_text()
assert source.startswith(pin), 'pin is not an exact prefix'
assert (base/'Attempt.lean.exit').read_text().strip()=='0'
assert (base/'Attempt.lean.log').stat().st_mtime >= (base/'Attempt.lean').stat().st_mtime
imports=re.findall(r'^import (\S+)',source,re.M)
assert imports==['DrEquiv']
forbidden=re.findall(r'\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b',source)
assert not forbidden
assert not re.search(r'\b(?:error|warning):',log)
allowed={'propext','Classical.choice','Quot.sound'}
records={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
    axioms=[] if m[2] is None else [a.strip() for a in m[2].split(',') if a.strip()]
    assert set(axioms)<=allowed, (m[1],axioms)
    assert m[1] not in records
    records[m[1]]=axioms
# Namespace/section tracker for the small, directly written Lean artifact.
blocks=[]
declarations={}
for lineno,line in enumerate(source.splitlines(),1):
    m=re.match(r'^(namespace|section)\s*(\S*)',line)
    if m:
        blocks.append((m[1],m[2]));continue
    if re.match(r'^end(?:\s|$)',line):
        blocks.pop();continue
    m=re.match(r'^(?:noncomputable )?(?:def|theorem|abbrev) (\w+)',line)
    if m:
        ns='.'.join(name for typ,name in blocks if typ=='namespace')
        declarations[ns+'.'+m[1]]=lineno
assert not blocks
assert set(declarations)<=set(records), sorted(set(declarations)-set(records))
assert (base/'numerics/cover_probe.exit').read_text().strip()=='0'
num=json.loads((base/'numerics/cover_results.json').read_text())
assert num['peak_rss_kib']*1024 < 4_000_000_000
assert num['torus_arithmetic']
assert num['carrier_dimension']==3648
report=dict(closedGoal='none',exitCode=0,pin_exact_prefix=True,imports=imports,
    forbidden_tokens=forbidden,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    local_declarations=declarations,local_declaration_count=len(declarations),
    axiom_record_count=len(records),axioms=records,
    numeric_exit=0,numeric_peak_rss_kib=num['peak_rss_kib'],
    numeric_warning=num['warning'])
(base/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['closedGoal','exitCode','pin_exact_prefix','source_sha256',
    'local_declaration_count','axiom_record_count','numeric_exit','numeric_peak_rss_kib']},indent=2))
print('Declaration locations:',json.dumps({k:v for k,v in declarations.items() if '.RefuteR2.' in k},indent=2))
