#!/usr/bin/env python3
"""Read-only source/log audit; writes only this round-one audit record."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'Attempt.lean'
PIN = ROOT / 'AHP/round7/s1-odd/pin/Statement.lean'
OLD_PIN = ROOT / 'AHP/round3/s1-proper/pin/Statement.lean'
OLD_ATTEMPT = ROOT / 'AHP/round3/s1-proper/r1-refute/Attempt.lean'
PREVIOUS = ROOT / 'AHP/round7/s1-odd/proof/Attempt.lean'


def digest(data):
    return hashlib.sha256(data).hexdigest()


source = SOURCE.read_bytes()
pin = PIN.read_bytes()
old_pin = OLD_PIN.read_bytes()
old_attempt = OLD_ATTEMPT.read_bytes()
prelude = b'import D1Final\nimport GdPlaq\n'
assert pin.startswith(old_pin)
assert digest(pin) == '0c7cc8458e7d862e549c8e091325d906c3c448fb0ac7f08c9827a62cac9f3e4f'
assert source.startswith(prelude + pin)
start = b'/-! ## Locality: corner and all selectors'
stop = b'/-- Exact pinned negative goal.'
helpers = old_attempt[old_attempt.index(start):old_attempt.index(stop)]
assert helpers in source
text = source.decode()
log_path = SOURCE.with_suffix('.lean.log')
exit_path = SOURCE.with_suffix('.lean.exit')
log = log_path.read_text()
assert exit_path.read_text().strip() == '0'
assert SOURCE.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
assert not re.search(r'\b(error|warning):', log)
records = re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M)
assert len(records) == len(re.findall(r'^#print axioms ', text, re.M))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
dependencies = {}
for name, deps in records:
    used = {d.strip() for d in deps.split(',') if d.strip()}
    assert used <= allowed, (name, used)
    assert name not in dependencies, name
    dependencies[name] = sorted(used)

# All locally declared definitions and helper/main theorems have prints.
local_names = re.findall(r'^(?:noncomputable )?(?:def|theorem|lemma)\s+(\S+)', text, re.M)
for name in local_names:
    assert any(full.endswith('.' + name) for full in dependencies), name
for name, goal in [('goal1_proved', 'Goal1'), ('goal2_proved', 'Goal2')]:
    assert f'theorem {name} : {goal} :=' in text
    assert 'Round7.S1Odd.' + name in dependencies
assert 'P428TouchFourAt ell hell a := Iff.rfl' in text

forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
assert not forbidden, forbidden
imports = []
for module in re.findall(r'^import\s+(\S+)\s*$', text, re.M):
    path = ROOT / 'lean/src' / (module.replace('.', '/') + '.lean')
    assert path.is_file(), module
    imports.append({'module': module, 'source': str(path.relative_to(ROOT)), 'sha256': digest(path.read_bytes())})

# Remove only the outer fixed-parameter binders and compare the remaining body.
old = old_pin.decode()
old_body = old.split('def P428TouchFour : Prop :=', 1)[1].split('/-- The actual changed-operator', 1)[0]
old_body = old_body.split('0 < a →', 1)[1]
new_body = pin.decode().split('def P428TouchFourAt (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=', 1)[1]
new_body = new_body.split('/-- Every blocking factor', 1)[0]
assert ''.join(old_body.split()) == ''.join(new_body.split())

report = {
    'file': str(SOURCE.relative_to(ROOT)),
    'command': 'AHP/round3/lean1.sh AHP/round7/s1-odd/r1/Attempt.lean',
    'exit_code': 0,
    'errors': 0,
    'warnings': 0,
    'source_sha256': digest(source),
    'log_sha256': digest(log_path.read_bytes()),
    'pin_sha256': digest(pin),
    'previous_proof_sha256': digest(PREVIOUS.read_bytes()),
    'pin_unchanged': True,
    'round3_pin_is_prefix_of_round7_pin': True,
    'pin_verbatim_after_frozen_import_preamble': True,
    'pin_byte_offset': len(prelude),
    'preamble': prelude.decode(),
    'round3_helper_block_verbatim': True,
    'helper_block_sha256': digest(helpers),
    'slice_body_same_modulo_whitespace': True,
    'mass_window': '0 < a < 4',
    'closed_goals': {'Round7.S1Odd.Goal1': 'Round7.S1Odd.goal1_proved', 'Round7.S1Odd.Goal2': 'Round7.S1Odd.goal2_proved'},
    'local_declarations_with_dependency_prints': len(local_names),
    'dependency_record_count': len(records),
    'dependencies': dependencies,
    'forbidden_raw_tokens': forbidden,
    'imports': imports,
    'fresh_log_and_exit': True,
    'verification_scope': 'Builder compile and source audit; independent workflow verification remains separate.'
}
(HERE / 'AUDIT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in {'dependencies', 'imports'}}, indent=2))
