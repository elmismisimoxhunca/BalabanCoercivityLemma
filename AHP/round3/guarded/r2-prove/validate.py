#!/usr/bin/env python3
"""Static audit of this attempt and its final shared-wrapper compile artifacts."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[4]
base = Path(__file__).resolve().parent
source = base / 'Attempt.lean'
pin = root / 'AHP/round3/guarded/pin/Statement.lean'
log = base / 'Attempt.lean.log'
exit_file = base / 'Attempt.lean.exit'
raw = source.read_bytes()
text = raw.decode()
output = log.read_text()
checks = {}
checks['pin_byte_prefix'] = raw.startswith(pin.read_bytes())
checks['imports'] = re.findall(r'^import (.+)$', text, re.M)
checks['frozen_imports_only'] = checks['imports'] == ['DrEquiv']
checks['forbidden_token_hits'] = re.findall(
    r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text
)
checks['exit_code'] = int(exit_file.read_text().strip())
checks['timestamps_ordered'] = source.stat().st_mtime_ns <= log.stat().st_mtime_ns <= exit_file.stat().st_mtime_ns
checks['diagnostics'] = [line for line in output.splitlines() if re.search(r': (?:error|warning)(?:\(|:)', line)]

# These sources use ordinary namespace/section/end blocks, without mutual blocks.
stack = []
declarations = {}
for lineno, line in enumerate(text.splitlines(), 1):
    m = re.match(r'^namespace (\S+)', line)
    if m:
        stack.append(('namespace', m.group(1)))
        continue
    m = re.match(r'^section(?: (\S+))?\s*$', line)
    if m:
        stack.append(('section', m.group(1)))
        continue
    m = re.match(r'^end(?: (\S+))?\s*$', line)
    if m:
        assert stack, ('unmatched end', lineno)
        kind, name = stack.pop()
        assert m.group(1) is None or m.group(1) == name, ('mismatched end', lineno, name)
        continue
    m = re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma) (\S+)', line)
    if m:
        ns = '.'.join(name for kind, name in stack if kind == 'namespace')
        declarations[ns + '.' + m.group(1)] = lineno
assert not stack

records = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output):
    records[m.group(1)] = [] if m.group(2) is None else [a.strip() for a in m.group(2).split(',') if a.strip()]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
checks['local_declaration_count'] = len(declarations)
checks['dependency_record_count'] = len(records)
checks['missing_dependency_records'] = sorted(set(declarations) - set(records))
checks['nonstandard_dependencies'] = {n: a for n, a in records.items() if not set(a) <= allowed}
checks['declaration_lines'] = declarations
checks['source_sha256'] = hashlib.sha256(raw).hexdigest()
checks['pin_sha256'] = hashlib.sha256(pin.read_bytes()).hexdigest()
checks['log_sha256'] = hashlib.sha256(log.read_bytes()).hexdigest()
checks['main_declaration'] = 'AdalyFormal.Round3.Guarded.R2Prove.goalPos2_of_inverse_boundary_jetInputZero'
checks['main_dependencies'] = records.get(checks['main_declaration'])
checks['all_pass'] = all([
    checks['pin_byte_prefix'], checks['frozen_imports_only'],
    not checks['forbidden_token_hits'], checks['exit_code'] == 0,
    checks['timestamps_ordered'], not checks['diagnostics'],
    not checks['missing_dependency_records'], not checks['nonstandard_dependencies'],
    checks['main_declaration'] in records,
])
(base / 'VALIDATION.json').write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps({k: v for k, v in checks.items() if k != 'declaration_lines'}, indent=2))
assert checks['all_pass'], 'Final artifact checks failed; see VALIDATION.json'
