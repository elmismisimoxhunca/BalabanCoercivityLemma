"""Check R2 handoff without mutating the already accepted R1 artifacts."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
SHARED = ROOT / 'AHP/round13/shared/trial'
R1 = ROOT / 'AHP/round13/trial/r1'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ACCEPTED = '65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b'
NEW = ['trialVector_norm_sq', 'trialVector_ne_zero', 'trial_rayleigh',
       'rightStar_negative_halfpi', 'rightStar_physical_halfpi',
       'cofinal_rightStar_paths_halfpi']
PREFIX = 'AdalyFormal.Round13.Trial.R2.'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_certificate(source):
    data = source.read_bytes()
    text = data.decode()
    assert re.findall(r'^import (.+)$', text, re.M) == ['DrEquiv']
    forbidden = re.findall(
        r'\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|'
        r'run_tac|run_elab|elab|macro|syntax|initialize)\b', text)
    assert not forbidden, forbidden
    assert Path(str(source) + '.exit').read_text().strip() == '0'
    log_path = Path(str(source) + '.log')
    log = log_path.read_text()
    assert not re.search(r'\berror(?:\([^\n]*?\))?:', log)
    assert not re.search(r'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler', log)
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    records = [(name, [x.strip() for x in xs.split(',') if x.strip()])
               for name, xs in matches]
    records += [(name, []) for name in
                re.findall(r"'([^']+)' does not depend on any axioms", log)]
    for name, dependencies in records:
        assert set(dependencies) <= ALLOWED, (name, dependencies)
    commands = re.findall(r'^#print axioms (\S+)', text, re.M)
    assert len(commands) == len(records), (len(commands), len(records))
    # Every printed name, including short namespace-local names, must be accounted for.
    available = Counter(name for name, _ in records)
    for command in commands:
        candidates = [name for name in available if available[name] and
                      (name == command or name.endswith('.' + command))]
        assert candidates, command
        available[candidates[0]] -= 1
    table = dict(records)
    return {
        'source': str(source.relative_to(ROOT)), 'source_sha256': sha(data),
        'log_sha256': sha(log_path.read_bytes()), 'exit': 0,
        'lines': len(text.splitlines()), 'axiom_records': len(records),
        'warnings': len(re.findall(r': warning:', log)),
        'standard_axioms_only': True, 'forbidden_tokens': [],
    }, table


manifest = json.loads((OUT / 'COPIES.json').read_text())
base = (R1 / 'Trial.lean').read_bytes()
assert sha(base) == ACCEPTED == manifest['source_sha256']
assert len(base) == manifest['prefix_bytes']
appendix = (OUT / 'HandoffBody.lean.txt').read_bytes()
assert sha(appendix) == manifest['appendix_sha256']
assert appendix == (SHARED / 'R2_HandoffBody.lean.txt').read_bytes()
local = OUT / 'Trial.lean'
shared = SHARED / 'R2_Trial.lean'
assert local.read_bytes() == shared.read_bytes() == base + appendix

# The original builder, published certificate and independent reviewer copy
# remain unchanged, retain their clean exits and retain standard dependency records.
inherited = []
for path in [R1 / 'Trial.lean', SHARED / 'R1_Trial.lean', R1 / 'Trial.verify.lean']:
    assert path.read_bytes() == base
    summary, _ = check_certificate(path)
    inherited.append(summary)

# Recheck all five historical interfaces in the accepted prefix.
fragments = []
for entry in json.loads((R1 / 'COPIES.json').read_text()):
    original = (ROOT / entry['source']).read_bytes()
    assert sha(original) == entry['source_sha256']
    start = len(''.join(base.decode().splitlines(keepends=True)
                        [:entry['destination_first_line'] - 1]).encode())
    part = base[start:start + entry['fragment_bytes']]
    assert sha(part) == entry['fragment_sha256']
    assert part in original
    fragments.append({'source': entry['source'], 'verified_verbatim': True})

# P1's type is unchanged from the requested GAPS statement, not just similarly named.
gaps = (ROOT / 'AHP/round12/shared/GAPS.md').read_text()
expected = gaps.split('-- Negative direction at HALF pi, not merely at pi.\n', 1)[1].split('\n\n', 1)[0]
actual = appendix.decode().split('theorem rightStar_negative_halfpi :\n', 1)[1].split(' :=', 1)[0]
assert re.sub(r'\s', '', actual) == re.sub(r'\s', '', expected)

files = []
for path in [local, shared]:
    summary, records = check_certificate(path)
    assert all(PREFIX + short in records for short in NEW)
    assert len([name for name in records if name.startswith(PREFIX)]) == len(NEW)
    assert len([name for name in records if name.startswith('AdalyFormal.Round13.Trial.')
                and not name.startswith(PREFIX)]) == 91
    summary['new_declarations'] = {
        short: {'line': next(i for i, line in enumerate(path.read_text().splitlines(), 1)
                             if i > manifest['prefix_lines'] and line.startswith('theorem ' + short + ' ')),
                'axioms': records[PREFIX + short]}
        for short in NEW
    }
    files.append(summary)

result = {
    'status': 'PASS', 'scope': 'P1 only; R2 is a handoff built on accepted R1, not P2/P3/GoalNeg2',
    'r1_prefix_verbatim': True, 'byte_identical_publication': True,
    'p1_type_matches_requested_statement': True,
    'inherited_certificates': inherited, 'inherited_interface_checks': fragments,
    'files': files, 'numerical_proof_dependency': False,
    'review_boundary': 'R1 was independently accepted; R2 appendix has two builder executions, not independent review.',
    'initial_attempt': 'Exit 1 from a missing namespace opening; corrected before both accepted final compiles.',
}
encoded = json.dumps(result, indent=2) + '\n'
(OUT / 'AUDIT.json').write_text(encoded)
(SHARED / 'R2_AUDIT.json').write_text(encoded)
print(json.dumps({'status': 'PASS', 'new_declarations': len(NEW),
                  'axiom_records_per_final_file': files[0]['axiom_records'],
                  'r1_unchanged': True, 'p1_exact': True, 'scope': result['scope']}, indent=2))
