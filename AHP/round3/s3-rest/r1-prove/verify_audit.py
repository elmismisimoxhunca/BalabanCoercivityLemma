"""Independent source/log audit; no numerical model and no Lean invocation."""
from pathlib import Path
import collections
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
pin_path = HERE.parent / 'pin/Statement.lean'
attempt_path = HERE / 'Attempt.lean'
copy_path = HERE / 'Attempt.verify.lean'
log_path = HERE / 'Attempt.verify.lean.log'
exit_path = HERE / 'Attempt.verify.lean.exit'
pin, attempt, copy = [p.read_text() for p in (pin_path, attempt_path, copy_path)]
log = log_path.read_text()
r2_pin = (ROOT / 'AHP/round2/s3-normalisation/pin/Statement.lean').read_text()
r2_proof = (ROOT / 'AHP/round2/s3-normalisation/r1-prove/Attempt.lean').read_text()

# Comments are not stripped for the prohibited-word scan: this is stricter.
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', copy)
# Resolve ordinary namespace blocks and collect every explicit local declaration/print.
ns = []
decls = []
prints = []
for n, line in enumerate(copy.splitlines(), 1):
    m = re.fullmatch(r'namespace (\S+)', line)
    if m:
        ns.append(m[1])
    if re.fullmatch(r'end(?: \S+)?', line):
        ns.pop()
    m = re.match(r'(?:(?:noncomputable|private|protected) )*(def|abbrev|theorem|lemma|inductive|structure) (\S+)', line)
    if m:
        decls.append(('.'.join(ns + [m[2]]), m[1], n))
    m = re.fullmatch(r'#print axioms (\S+)', line)
    if m:
        prints.append(m[1] if m[1].startswith('AdalyFormal.') else '.'.join(ns + [m[1]]))

records = re.findall(r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M)
empty_records = re.findall(r"^'(.+)' does not depend on any axioms", log, re.M)
records += [(n, '') for n in empty_records]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad_axioms = [(n, a) for n, a in records if set(a.replace('\n', '').replace(' ', '').split(',')) - allowed - {''}]
record_names = [n for n, _ in records]
main = 'AdalyFormal.Round3.S3Rest.goalPos2_proved'
main_header = re.findall(r'^theorem goalPos2_proved[^\n]*', copy, re.M)
# Range endpoints are declaration boundaries, independent of whitespace formatting.
start = 'abbrev Fine'
end = '\nend AdalyFormal.Round2.S3Pin'
dict3 = pin[pin.index(start):pin.index(end)]
r2_start = r2_pin.index(start)
r2_end = r2_pin.index('\n/--', r2_pin.index('IsUnit (PrintedG1inv P r) ∧ IsUnit (PrintedN P r)'))
dict2 = r2_pin[r2_start:r2_end].rstrip()
block = ''.join(r2_proof.splitlines(keepends=True)[358:820])
checks = {
    'byte_identical_copy': attempt_path.read_bytes() == copy_path.read_bytes(),
    'pin_byte_identical_prefix': copy_path.read_bytes().startswith(pin_path.read_bytes()),
    'pin_whitespace_normalized_prefix': ''.join(copy[:len(pin)].split()) == ''.join(pin.split()),
    'round2_dictionary_whitespace_identical': ''.join(dict2.split()) == ''.join(dict3.split()),
    'round2_proof_block_byte_identical': block in copy,
    'sole_import_ZT5A': re.findall(r'^import (.+)$', copy, re.M) == ['ZT5A'],
    'main_header_exact': main_header == ['theorem goalPos2_proved : GoalPos2 := by'],
    'main_namespace_exact': [(name, kind) for name, kind, _ in decls if name.endswith('.goalPos2_proved')] == [(main, 'theorem')],
    'no_ambient_variables_or_local_notation': not re.search(r'^(?:variable|variables|section|local|notation|macro|elab|syntax)\b', copy, re.M),
    'no_duplicate_explicit_declarations': len(decls) == len(set(n for n, _, _ in decls)),
    'exit_zero': exit_path.read_text().strip() == '0',
    'no_errors': not re.search(r'\berror:', log),
    'all_axioms_allowed': not bad_axioms,
    'all_prints_accounted_for': collections.Counter(prints) == collections.Counter(record_names),
    'every_explicit_declaration_printed': set(n for n, _, _ in decls) <= set(prints),
    'main_print_present': main in record_names,
    'no_forbidden_tokens_raw': not forbidden,
}
result = {
    'checks': checks,
    'all_pass': all(checks.values()),
    'exitCode': int(exit_path.read_text()),
    'declarations': len(decls),
    'requestedPrints': len(prints),
    'dependencyRecords': len(records),
    'warnings': len(re.findall(r'\bwarning:', log)),
    'badAxioms': bad_axioms,
    'forbiddenTokens': forbidden,
    'mainHeader': main_header,
    'mainAxioms': [a for n, a in records if n == main],
    'sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (pin_path, attempt_path, copy_path, log_path, exit_path)},
    'pinBytes': len(pin_path.read_bytes()),
    'attemptBytes': len(copy_path.read_bytes()),
}
(HERE / 'Attempt.verify.audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert result['all_pass'], 'Independent verification failed'
