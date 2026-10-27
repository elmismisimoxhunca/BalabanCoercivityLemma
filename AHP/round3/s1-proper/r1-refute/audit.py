#!/usr/bin/env python3
"""Read-only source/log checks; writes only this attempt's audit.json.
Run after lean1.sh returns. Does not invoke Lean or build anything.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
src_path = HERE/'Attempt.lean'
src = src_path.read_text()
pin_path = HERE.parent/'pin/Statement.lean'
pin = pin_path.read_text()
log = (HERE/'Attempt.lean.log').read_text()
exit_code = int((HERE/'Attempt.lean.exit').read_text().strip())

def pin_block(s):
    return s.split('namespace Round3.S1Proper\n', 1)[1].split('-- Well-formedness', 1)[0]

def declaration(s, name):
    # All inspected declaration bodies are followed by an empty line.
    m = re.search(r'(?ms)^(?:theorem|def) '+re.escape(name)+r'\b.*?(?=\n\n)', s)
    assert m, name
    return m.group()

names = re.findall(r'^(?:theorem|def) (\w+)', src, re.M)
records = re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S | re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
parsed = {name: [x.strip() for x in axioms.split(',') if x.strip()]
          for name, axioms in records}
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', src)
imports = re.findall(r'^import (\S+)', src, re.M)
old = (ROOT/'AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean').read_text()
coverage_helpers = ['four_touch_cubeBond_of_transverse', 'slabNv_transverse', 'slabNv_coversFour']
checks = {
    'exit_zero': exit_code == 0,
    'pin_declaration_block_byte_identical': pin_block(pin) == pin_block(src),
    'exact_goal_header': 'theorem goalNeg1_proved : GoalNeg1 := by' in src,
    'no_extra_variable_context': src.count('variable ') == 1,
    'all_local_declarations_printed': all('Round3.S1Proper.'+n in parsed for n in names),
    'axioms_only_allowed': bool(records) and all(set(xs) <= allowed for xs in parsed.values()),
    'no_errors_or_warnings': not re.search(r'\b(?:error|warning):', log),
    'no_forbidden_tokens': not forbidden,
    'imports_only_frozen': all((ROOT/'lean/src'/Path(*n.split('.'))).with_suffix('.lean').exists()
                               for n in imports),
    'round2_coverage_helpers_verbatim': all(declaration(src,n) == declaration(old,n)
                                          for n in coverage_helpers),
}
result = {
    'checks': checks,
    'all_pass': all(checks.values()),
    'exit_code': exit_code,
    'imports': imports,
    'local_declarations': names,
    'dependency_record_count': len(records),
    'main_dependency_record': parsed.get('Round3.S1Proper.goalNeg1_proved'),
    'forbidden_hits': forbidden,
    'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in [src_path, HERE/'Attempt.lean.log', HERE/'search.py', HERE/'search.json']},
    'pin_sha256': hashlib.sha256(pin_path.read_bytes()).hexdigest(),
}
(HERE/'audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
assert result['all_pass'], checks
