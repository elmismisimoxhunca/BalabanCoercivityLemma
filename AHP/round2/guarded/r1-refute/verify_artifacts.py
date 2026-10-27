#!/usr/bin/env python3
"""Local artifact audit. Does not compile Lean or prove a mathematical claim."""
import hashlib
import json
import re
from pathlib import Path
root=Path(__file__).resolve().parent
pin=(root.parent/'pin/Statement.lean').read_text()
source=(root/'Attempt.lean').read_text()
marker='end AdalyFormal.Round2.Guarded.Pin\n'
prefix=source[:source.index(marker)+len(marker)]
assert prefix.replace('import GdR6b\n','',1)==pin
assert (root/'Attempt.lean.exit').read_text().strip()=='0'
log=(root/'Attempt.lean.log').read_text()
assert not re.search(r'\b(error|warning):|sorryAx',log)
records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
allowed={'propext','Classical.choice','Quot.sound'}
for name,body in records:
    assert {s.strip() for s in body.split(',')}<=allowed,(name,body)
theorems=re.findall(r'^theorem (\w+)',source,re.M)
printed={name.split('.')[-1] for name,_ in records}
assert all(name in printed for name in theorems)
forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',source)
assert not forbidden
imports=re.findall(r'^import (.*)$',source,re.M)
assert imports==['DrEquiv','GdR6b']
for f in ['probe_assembled','probe_separation','audit_numerics']:
    assert (root/'numerics'/f'{f}.exit').read_text().strip()=='0'
main='AdalyFormal.Round2.Guarded.RefuteR1.pencil_failure_iff_second_jet'
body=next(body for name,body in records if name==main)
result=dict(closedGoal='none',pin_copy_exact=True,compile_exit=0,
    lean_sha256=hashlib.sha256(source.encode()).hexdigest(),
    imports=imports,forbidden_tokens=forbidden,axiom_record_count=len(records),
    local_theorem_count=len(theorems),all_local_theorems_printed=True,
    mainDeclaration=main,
    axiomLine=f"'{main}' depends on axioms: ["+', '.join(s.strip() for s in body.split(','))+']',
    note='All goals are preserved; the main declaration is only a pointwise equivalence, not a negative goal.')
(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
