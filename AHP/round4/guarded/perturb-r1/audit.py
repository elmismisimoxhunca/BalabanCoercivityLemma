#!/usr/bin/env python3
"""Audit the final perturbation attempt; writes only beside this script."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[3]
source = here / 'Attempt.lean'
pin = root / 'AHP/round3/guarded/pin/Statement.lean'
log = here / 'Attempt.lean.log'
exit_file = here / 'Attempt.lean.exit'
raw = source.read_bytes()
text = raw.decode()
log_text = log.read_text()
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
imports = re.findall(r'^import\s+(.+)$', text, flags=re.M)
declarations = re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+(\w+)', text, flags=re.M)
prints = re.findall(r'^#print axioms\s+([\w.]+)', text, flags=re.M)
records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log_text)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axioms_ok = all(set(filter(None, map(str.strip, deps.split(',')))) <= allowed for _, deps in records)
printed_suffixes = {name.rsplit('.', 1)[-1] for name in prints}
recorded_suffixes = {name.rsplit('.', 1)[-1] for name, _ in records}
# All local declarations here have at least one permitted dependency.
main = 'AdalyFormal.Round4.Guarded.PerturbR1.nv_guard_no_uniform_response_gap'
checks = {
    'pin_exact_byte_prefix': raw.startswith(pin.read_bytes()),
    'pin_sha256': hashlib.sha256(pin.read_bytes()).hexdigest(),
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'imports': imports,
    'only_frozen_DrEquiv_import': imports == ['DrEquiv'],
    'forbidden_tokens': forbidden,
    'exit_code': int(exit_file.read_text().strip()),
    'diagnostics': re.findall(r'^.*(?:error:|warning:).*$', log_text, flags=re.M),
    'declarations': len(declarations),
    'print_directives': len(prints),
    'dependency_records': len(records),
    'all_declarations_have_prints': set(declarations) <= printed_suffixes,
    'all_declarations_have_records': set(declarations) <= recorded_suffixes,
    'all_dependencies_permitted': axioms_ok,
    'main_declaration': main,
    'main_dependency_record': next(({'name': n, 'axioms': a} for n, a in records if n == main), None),
    'timestamp_order': source.stat().st_mtime_ns <= log.stat().st_mtime_ns <= exit_file.stat().st_mtime_ns,
    'closedGoal': 'none',
}
checks['passed'] = all([
    checks['pin_exact_byte_prefix'], checks['only_frozen_DrEquiv_import'], not forbidden,
    checks['exit_code'] == 0, not checks['diagnostics'],
    checks['all_declarations_have_prints'], checks['all_declarations_have_records'],
    checks['all_dependencies_permitted'], bool(checks['main_dependency_record']), checks['timestamp_order'],
])
(here / 'CHECKS.json').write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps(checks, indent=2))
raise SystemExit(0 if checks['passed'] else 1)
