#!/usr/bin/env python3
"""Read-only source/log checks; writes audit.json only in this track."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD_PIN = ROOT / 'AHP/round3/s1-proper/pin/Statement.lean'
OLD_PROOF = ROOT / 'AHP/round3/s1-proper/r1-refute/Attempt.lean'
PIN = HERE / 'pin/Statement.lean'
PROOF = HERE / 'proof/Attempt.lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def norm(text):
    return ' '.join(text.split())


old_pin = OLD_PIN.read_bytes()
pin = PIN.read_bytes()
proof = PROOF.read_bytes()
old_proof = OLD_PROOF.read_text()
helpers = old_proof[old_proof.index('/-! ## Locality: corner and all selectors'):
                    old_proof.index('/-- Exact pinned negative goal.')].encode()
assert pin.startswith(old_pin), 'Round-3 pin changed'
assert proof.startswith(b'import D1Final\nimport GdPlaq\n' + pin), 'Round-7 pin changed in proof'
assert proof.count(helpers) == 1, 'Round-3 helper proofs changed'
old_body = old_pin.decode().split('def P428TouchFour : Prop :=\n', 1)[1].split(
    '/-- The actual changed-operator headline', 1)[0]
old_body = old_body.split('\n', 1)[1]
new_body = pin.decode().split('def P428TouchFourAt (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=\n', 1)[1].split(
    '/-- Every blocking factor', 1)[0]
assert norm(old_body) == norm(new_body), 'Slice body changed'

report = {
    'round3_pin_byte_prefix': True,
    'round7_pin_verbatim_in_proof': True,
    'round3_helpers_verbatim': True,
    'slice_body_same_modulo_whitespace': True,
    'round3_pin_sha256': sha(old_pin),
    'round3_helper_block_sha256': sha(helpers),
    'mass_range': '0 < a < 4',
    'goals': {
        'Round7.S1Odd.Goal1': 'Round7.S1Odd.goal1_proved',
        'Round7.S1Odd.Goal2': 'Round7.S1Odd.goal2_proved',
    },
    'files': [],
}
for src in (PIN, PROOF):
    data = src.read_bytes()
    text = data.decode()
    imports = re.findall(r'^import (\S+)$', text, re.M)
    import_records = []
    for mod in imports:
        frozen = ROOT / 'lean/src' / (mod.replace('.', '/') + '.lean')
        assert frozen.is_file(), f'Non-frozen import {mod}'
        import_records.append({'module': mod, 'source': str(frozen.relative_to(ROOT)),
                               'source_sha256': sha(frozen.read_bytes())})
    # Strong raw-text check suffices for these files: no comments need stripping.
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
    assert not forbidden, forbidden
    log_path = Path(str(src) + '.log')
    exit_path = Path(str(src) + '.exit')
    log = log_path.read_text()
    assert exit_path.read_text().strip() == '0'
    assert src.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
    assert not re.search(r'\b(?:error|warning):', log)
    records = re.findall(r"'([^\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(records) == len(re.findall(r'^#print axioms ', text, re.M))
    dependencies = {}
    for name, deps in records:
        names = {s.strip() for s in deps.split(',') if s.strip()}
        assert names <= ALLOWED, (name, names)
        dependencies[name] = sorted(names)
    if src == PROOF:
        for name in (*report['goals'].values(), 'Round7.S1Odd.not_touchFour_every_ell',
                     'Round7.S1Odd.headline_iff_slices'):
            assert name in dependencies
    report['files'].append({
        'path': str(src.relative_to(ROOT)), 'source_sha256': sha(data),
        'command': 'AHP/round3/lean1.sh ' + str(src.relative_to(ROOT)),
        'exit_code': 0, 'warnings': 0, 'errors': 0,
        'dependency_records': len(records), 'dependencies': dependencies,
        'log_sha256': sha(log_path.read_bytes()), 'imports': import_records,
        'forbidden_raw_tokens': forbidden,
    })
(HERE / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))
for f in report['files']:
    print(f"{f['path']}: exit=0, records={f['dependency_records']}, warnings=0, errors=0")
