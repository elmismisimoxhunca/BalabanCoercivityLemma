#!/usr/bin/env python3
"""Static verification evidence, not a numerical operator model or a Lean proof."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
pin_path = here.parent / 'pin' / 'Statement.lean'
attempt_path = here / 'Attempt.lean'
pin = pin_path.read_bytes()
attempt = attempt_path.read_bytes()
source = attempt.decode()
log = (here / 'Attempt.verify.log').read_text()
exit_code = int((here / 'Attempt.verify.exit').read_text().strip())
ns = 'AdalyFormal.Round2.S3Pin.'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = re.findall(r"^'(.*?)' depends on axioms:\s*\[([^\]]*)\]", log, re.M)
prints = re.findall(r'^#print axioms (\S+)\s*$', source, re.M)
new_source = source[len(pin.decode()):]
new_declarations = re.findall(r'^(?:theorem|lemma)\s+(\S+)', new_source, re.M)
forbidden = re.findall(r'\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source)
bad_axioms = {name: sorted(set(x.strip() for x in axioms.split(',') if x.strip()) - allowed)
              for name, axioms in records}
bad_axioms = {k: v for k, v in bad_axioms.items() if v}
record_names = [name for name, _ in records]
result = {
    'pin_sha256': hashlib.sha256(pin).hexdigest(),
    'attempt_sha256': hashlib.sha256(attempt).hexdigest(),
    'verify_log_sha256': hashlib.sha256(log.encode()).hexdigest(),
    'verify_exit': exit_code,
    'pin_bytes': len(pin),
    'pin_lines': len(pin.splitlines()),
    'byte_identical_pin_prefix': attempt.startswith(pin),
    'whitespace_normalized_pin_prefix_equal': re.sub(rb'\s+', b'', attempt[:len(pin)]) == re.sub(rb'\s+', b'', pin),
    'imports': re.findall(r'^import\s+(.+)$', source, re.M),
    'main_signature': re.findall(r'^theorem goalPos1_proved[^\n]*', source, re.M),
    'main_signature_is_literal_goal': 'theorem goalPos1_proved : GoalPos1 := by' in source,
    'new_declarations': len(new_declarations),
    'axiom_commands': len(prints),
    'axiom_records': len(records),
    'missing_axiom_records': sorted(set(prints) - set(record_names)),
    'unexpected_axiom_records': sorted(set(record_names) - set(prints)),
    'new_declarations_without_print': sorted(ns + name for name in new_declarations if ns + name not in prints),
    'nonstandard_axioms': bad_axioms,
    'forbidden_raw_tokens': forbidden,
    'warning_count': len(re.findall(r': warning:', log)),
    'error_count': len(re.findall(r': error:', log)),
    'main_axiom_records': [name + ': [' + axioms + ']' for name, axioms in records if name in {ns + 'goalPos1_proved', ns + 'goalPos2_proved'}],
}
assert exit_code == 0
assert result['byte_identical_pin_prefix'] and result['whitespace_normalized_pin_prefix_equal']
assert result['imports'] == ['ZT5A']
assert result['main_signature_is_literal_goal']
assert not forbidden and not bad_axioms
assert not result['missing_axiom_records'] and not result['unexpected_axiom_records']
assert not result['new_declarations_without_print']
assert len(records) == len(prints) == len(set(record_names)) == 59
assert result['error_count'] == 0
(here / 'Attempt.verify.audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
