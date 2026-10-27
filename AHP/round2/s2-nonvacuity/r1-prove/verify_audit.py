"""Independent textual and fresh-compiler-output audit; no numerical model."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[4]
base = Path(__file__).resolve().parent
pin_path = base.parent / 'pin/Statement.lean'
attempt_path = base / 'Attempt.lean'
pin = pin_path.read_text()
attempt = attempt_path.read_text()
stage = (root / 'AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean').read_text()
log = (base / 'Attempt.verify.log').read_text()
normalize = lambda s: re.sub(r'\s+', ' ', s).strip()

def definitions(text):
    # Each declaration in these files has no blank line in its body.
    # Stop at the first blank line, retaining the complete header and body.
    return {
        m.group(1): (m.group(0).rstrip(), text.count('\n', 0, m.start()) + 1)
        for m in re.finditer(r'^def ([^\s(]+)[^\n]*(?:\n(?!\s*\n)[^\n]+)*', text, re.M)
    }

pd, ad, sd = map(definitions, (pin, attempt, stage))
assert len(pd) == len(ad) == 14
matches = []
for name, (text, line) in pd.items():
    other, other_line = ad[name]
    matches.append({'name': name, 'pinLine': line, 'attemptLine': other_line,
                    'exact': text == other, 'whitespaceNormalized': normalize(text) == normalize(other)})
assert all(m['exact'] and m['whitespaceNormalized'] for m in matches)
stage_matches = {n: sd[n][0] == pd[n][0] for n in list(pd)[:8]}
assert all(stage_matches.values())
# Same local namespaces, opens and implicit-variable context before copied defs.
context = lambda s: s[s.index('set_option autoImplicit'):s.index('/-! ## Verbatim')]
assert context(pin) == context(attempt)

forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', attempt)
assert not forbidden
imports = re.findall(r'^import (\S+)$', attempt, re.M)
assert imports == ['ZT5A', 'D1Final', 'ZR8Class']
assert all((root / 'lean/src' / (n.replace('.', '/') + '.lean')).is_file() for n in imports)
assert re.search(r'^theorem goalPos1_proved : GoalPos1 := by$', attempt, re.M)
main = 'AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved'
assert f'{main} : GoalPos1' in log
assert len(re.findall(r'^namespace ', attempt, re.M)) == 1  # No nested namespace shadowing.
assert 'namespace AdalyFormal.AHP.Round2.S2Nonvacuity\n' in attempt

records = []
for m in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))", log, re.M):
    axioms = [] if m.group(3) else [x.strip() for x in m.group(2).split(',') if x.strip()]
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    records.append({'name': m.group(1), 'axioms': axioms})
assert len(records) == len(re.findall(r'^#print axioms ', attempt, re.M)) == 40
assert len({r['name'] for r in records}) == 40
assert any(r['name'] == main for r in records)
exit_code = int((base / 'Attempt.verify.exit').read_text())
assert exit_code == 0
assert not re.search(r'\b(?:warning|error):', log)

print(json.dumps({
    'attemptSha256': hashlib.sha256(attempt_path.read_bytes()).hexdigest(),
    'pinSha256': hashlib.sha256(pin_path.read_bytes()).hexdigest(),
    'exitCode': exit_code,
    'definitions': matches,
    'stageBDefinitionMatches': stage_matches,
    'identicalPredefinitionContext': True,
    'imports': imports,
    'forbiddenTokens': forbidden,
    'mainDeclaration': main,
    'exactDeclaredType': 'AdalyFormal.AHP.Round2.S2Nonvacuity.GoalPos1',
    'axiomRecords': records,
    'axiomRecordCount': len(records),
    'warningsOrErrors': False
}, indent=2))
