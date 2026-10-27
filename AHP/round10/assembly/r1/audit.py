#!/usr/bin/env python3
"""Artifact audit, explicitly NOT a GoalNeg2 proof audit."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SHARED = ROOT / 'AHP/round10/shared'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def compiled(path, expected=None):
    source = path.read_text()
    log_path = Path(str(path)+'.log')
    exit_path = Path(str(path)+'.exit')
    log = log_path.read_text()
    records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    deps = {name:set(filter(None,(t.strip() for t in raw.split(',')))) for name,raw in records}
    checks = dict(exit_zero=exit_path.read_text().strip()=='0',
        timestamps=path.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns,
        no_diagnostics=not re.search(r'\b(error|warning):|sorryAx',log),
        records_present=bool(records), allowed_axioms=all(v <= ALLOWED for v in deps.values()),
        no_forbidden_tokens=not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b|^\s*axiom\s',source,re.M))
    if expected is not None:
        checks['expected_declarations']=set(expected) <= deps.keys()
    return dict(path=str(path.relative_to(ROOT)),sha256=sha(path),checks=checks,
                axiom_records={k:sorted(v) for k,v in deps.items()}, pass_checks=all(checks.values()))

names=['eventually_ne_zero_of_normalized_limit','cofinal_of_eventual_subsequence',
       'even_radius_progression','nested_cofinal_of_eventual']
expected=['AdalyFormal.Round10.Assembly.'+n for n in names]
short=[compiled(HERE/'Cofinal.lean',expected),compiled(SHARED/'assembly/R1_Cofinal.lean',expected)]
shared=[compiled(SHARED/f'nonvanishing/R1_{n}.lean') for n in
        ['SourceDominance','RecurrenceNonvanishing','TransferNonvanishing']]
shared.append(compiled(SHARED/'dictionary/R1_Dictionary.lean'))
prefix=(ROOT/'AHP/round9/qualitative-r2/Attempt.lean').read_bytes()
assembled=bytearray(prefix)
for path in [HERE/'snap/SourceDominance.lean',HERE/'Cofinal.lean',HERE/'Glue.lean']:
    data=path.read_bytes()
    if data.startswith(b'import D1IVT\n'): data=data[len(b'import D1IVT\n'):]
    assembled.extend(b'\n'+data)
main=HERE/'Attempt.lean'
structure=dict(prefix_unchanged=main.read_bytes().startswith(prefix),
    exact_assembly=main.read_bytes()==bytes(assembled),
    shared_cofinal_identical=(HERE/'Cofinal.lean').read_bytes()==(SHARED/'assembly/R1_Cofinal.lean').read_bytes(),
    source_snapshot_identical=(HERE/'snap/SourceDominance.lean').read_bytes()==(SHARED/'nonvanishing/R1_SourceDominance.lean').read_bytes(),
    dictionary_shared_identical=(SHARED/'dictionary/R1_Dictionary.lean').read_bytes()==(ROOT/'AHP/round10/dictionary/r1/Actual.lean').read_bytes(),
    no_full_exit_file=not Path(str(main)+'.exit').exists(),
    imports=re.findall(r'^import (\S+)',main.read_text(),re.M)==['DrEquiv'],
    no_forbidden_tokens=not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by|extern|opaque)\b|^\s*axiom\s',main.read_text(),re.M))
numeric={str(p): (HERE/f'numerics/left_q2_R22_p{p}.exit').read_text().strip()=='0' for p in [140,190,220]}
out=dict(goalNeg2_proved=False,round9_premise_proved=False,concrete_glue_compiled=False,
    full_compilation_status='Two confirmed memory kills; no exit. Further large attempts stopped by coordinator.',
    assembled_sha256=sha(main),prefix_sha256=hashlib.sha256(prefix).hexdigest(),
    structure_checks=structure,compiled_short_files=short,reviewed_shared_files=shared,
    numerical_process_exit_zero=numeric,
    artifact_checks_pass=all(structure.values()) and all(x['pass_checks'] for x in short+shared) and all(numeric.values()))
(HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['compiled_short_files','reviewed_shared_files']},indent=2))
raise SystemExit(0 if out['artifact_checks_pass'] else 1)
