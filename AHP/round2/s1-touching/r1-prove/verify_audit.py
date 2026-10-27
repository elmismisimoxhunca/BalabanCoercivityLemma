#!/usr/bin/env python3
"""Text/log audit only; no numerical operator model and no Lean execution."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
pin_path = HERE.parent / 'pin/Statement.lean'
attempt_path = HERE / 'Attempt.lean'
pin = pin_path.read_text()
attempt = attempt_path.read_text()
log = (HERE / 'Attempt.verify.log').read_text()

# The full namespace prefix includes every pin definition, its context,
# comments, checks and dependency-print commands, before any attempt proof.
pin_body = pin.split('namespace Round2.S1\n', 1)[1].rsplit('end Round2.S1', 1)[0].strip()
attempt_body = attempt.split('namespace Round2.S1\n', 1)[1]
assert attempt_body.lstrip().startswith(pin_body)

def blocks(text):
    result = {}
    for match in re.finditer(r'^def (\S+).*?(?=\n\s*\n|\Z)', text, re.M | re.S):
        name = match.group(1)
        assert name not in result
        result[name] = match.group(0).rstrip()
    return result

pdefs, adefs = blocks(pin), blocks(attempt)
comparison = [{
    'name': name,
    'pin_line': pin[:pin.index(block)].count('\n') + 1,
    'attempt_line': attempt[:attempt.index(adefs[name])].count('\n') + 1,
    'byte_identical': block == adefs[name],
    'whitespace_normalised_identical': re.sub(r'\s+', '', block) == re.sub(r'\s+', '', adefs[name]),
} for name, block in pdefs.items()]
assert len(comparison) == 22
assert all(row['byte_identical'] for row in comparison)

# Four additional copied square-corner definitions are not in the pin.
s2 = (ROOT / 'AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean').read_text()
s2defs = blocks(s2)
extra = []
for name in sorted(adefs.keys() - pdefs.keys()):
    extra.append({'name': name, 'matches_stage_b_source': adefs[name] == s2defs[name]})
assert all(row['matches_stage_b_source'] for row in extra)

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = {}
for line in log.splitlines():
    m = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
    n = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
    if m:
        name, deps = m.groups()
        axioms = set(deps.split(', ')) if deps else set()
    elif n:
        name, axioms = n.group(1), set()
    else:
        continue
    assert name not in records
    assert axioms <= allowed, (name, axioms)
    records[name] = sorted(axioms)
local_names = re.findall(r'^(?:def|theorem|lemma) (\S+)', attempt, re.M)
missing = [name for name in local_names if 'Round2.S1.' + name not in records]
assert not missing
prints = re.findall(r'^#print axioms (\S+)', attempt, re.M)
assert len(prints) == len(records) == 72
assert len(local_names) == 67

forbidden = r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b'
hits = [{'line': attempt[:m.start()].count('\n') + 1, 'token': m.group()} for m in re.finditer(forbidden, attempt)]
assert not hits
imports = re.findall(r'^import (\S+)', attempt, re.M)
import_paths = [ROOT / 'lean/src' / (name.replace('.', '/') + '.lean') for name in imports]
assert all(p.is_file() for p in import_paths)
assert re.search(r'^theorem goalPos2_proved : GoalPos2 :=', attempt, re.M)
assert 'Round2.S1.goalPos2_proved : GoalPos2' in log
assert (HERE / 'Attempt.verify.exit').read_text().strip() == '0'
assert not re.search(r'\b(?:warning|error):', log)

report = {
    'exit_code': 0,
    'main_declaration': 'Round2.S1.goalPos2_proved',
    'main_type': 'Round2.S1.GoalPos2',
    'main_declaration_line': 689,
    'pin_namespace_prefix_byte_identical': True,
    'pin_definition_checks': comparison,
    'extra_helper_definition_checks': extra,
    'local_declarations': len(local_names),
    'dependency_records': len(records),
    'missing_dependency_records': missing,
    'all_dependencies_allowed': True,
    'main_axioms': records['Round2.S1.goalPos2_proved'],
    'raw_forbidden_token_hits': hits,
    'imports': imports,
    'all_imports_in_frozen_source_tree': True,
    'hashes': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in [pin_path, attempt_path, HERE/'Attempt.verify.log', HERE/'Attempt.verify.exit']},
}
(HERE / 'Attempt.verify.audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
