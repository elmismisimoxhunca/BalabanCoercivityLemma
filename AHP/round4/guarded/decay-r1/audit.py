from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
src_path = root / 'Attempt.lean'
log_path = root / 'Attempt.lean.log'
exit_path = root / 'Attempt.lean.exit'
pin_path = Path('AHP/round3/guarded/pin/Statement.lean')
src, log = src_path.read_text(), log_path.read_text()
pin = pin_path.read_bytes()
assert src_path.read_bytes().startswith(pin), 'pin differs'
assert exit_path.read_text().strip() == '0', 'compile failed'
assert not re.search(r'\b(error|warning)(?:\(|:)', log), 'compiler diagnostic'
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', src)
assert not forbidden, forbidden
imports = re.findall(r'^import\s+(.*)$', src, re.M)
assert imports == ['DrEquiv'], imports
for n in ['GoalPos1', 'GoalPos2', 'GoalNeg1', 'GoalNeg2']:
    assert len(re.findall(r'^def '+n+r'\b', src, re.M)) == 1, n

# Collect exact top-level declaration names through namespace and section scopes.
stack, declarations = [], []
for line in src.splitlines():
    m = re.fullmatch(r'namespace (\S+)\s*', line)
    if m:
        stack.append(('namespace', m.group(1)))
        continue
    m = re.fullmatch(r'section(?: (\S+))?\s*', line)
    if m:
        stack.append(('section', m.group(1)))
        continue
    m = re.fullmatch(r'end(?: (\S+))?\s*', line)
    if m:
        kind, name = stack.pop()
        assert m.group(1) is None or m.group(1) == name, (line, kind, name)
        continue
    m = re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma) (\S+)', line)
    if m:
        name = m.group(1)
        declarations.append('.'.join([name for kind, name in stack if kind == 'namespace'] + [name]))
assert not stack, stack
assert len(declarations) == len(set(declarations)), 'duplicate local declarations'

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log):
    deps = sorted(s.strip() for s in (m.group(2) or '').split(',') if s.strip())
    assert set(deps) <= allowed, (m.group(1), deps)
    assert m.group(1) not in records, 'duplicate print: '+m.group(1)
    records[m.group(1)] = deps
assert set(records) == set(declarations), (set(declarations)-set(records), set(records)-set(declarations))
assert len(re.findall(r'^#print axioms ', src, re.M)) == len(declarations)

# Check the most important reused operative declarations as exact blocks.
r1 = Path('AHP/round3/guarded/r1-prove/Attempt.lean').read_text()
r2 = Path('AHP/round3/guarded/r2-prove/Attempt.lean').read_text()
r3 = Path('AHP/round3/guarded/r3-prove/Attempt.lean').read_text()
def block(s, a, b):
    return s[s.index(a):s.index(b, s.index(a))]
blocks = {
    'jetInputZero': block(r2, 'def jetInputZero :', '/-- Same row proof'),
    'correction_kills_of_jet_translation': block(r2, 'theorem correction_kills_of_jet_translation', 'end Algebra'),
    'jet_translation_of_jetInputZero': block(r2, 'theorem jet_translation_of_jetInputZero', 'theorem correction_kills_jetInputZero'),
    'correction_kills_jetInputZero': block(r2, 'theorem correction_kills_jetInputZero', '/-- Exact input mask'),
    'relativeReturn': block(r1, 'noncomputable def relativeReturn', 'omit [FiniteDimensional'),
    'inverse_pairing': block(r3, 'theorem inverse_pairing', '/-- Testing against the actual range'),
}
for name, value in blocks.items():
    assert value in src, 'reused block changed: '+name

assert src_path.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
result = {
    'status': 'compiled-partial-only',
    'closedGoal': 'none',
    'finalFile': str(src_path.relative_to(Path.cwd())),
    'compiledAs': 'AHP/round4/guarded/decay-r1/Check04.lean',
    'compileCommand': 'AHP/round3/lean1.sh AHP/round4/guarded/decay-r1/Check04.lean',
    'promotion': 'Source and wrapper-created log/exit moved unchanged to Attempt.lean names after exit 0; no second compile of an unfinished path.',
    'exitCode': 0,
    'diagnostics': [],
    'sha256': hashlib.sha256(src_path.read_bytes()).hexdigest(),
    'pinSha256': hashlib.sha256(pin).hexdigest(),
    'pinExactBytePrefix': True,
    'goalDefinitionsUnchanged': True,
    'imports': imports,
    'forbiddenTokens': forbidden,
    'localDeclarationCount': len(declarations),
    'axiomRecordCount': len(records),
    'exactCopiedBlocks': list(blocks),
    'axioms': records,
    'mainDeclaration': 'AdalyFormal.Round4.Guarded.DecayR1.actual_return_norm_le_two_pass',
    'notes': 'AHP/round4/guarded/decay-r1/NOTES.md',
    'preliminaryAttempts': [
        {'file':'initial Attempt.lean', 'result':'foreground wrapper ended without exit record; empty log; no surviving process on two inspections; not relaunched'},
        {'file':'Check01.lean', 'exitCode':1, 'result':'type/elaboration errors; not accepted'},
        {'file':'Check02.lean', 'exitCode':1, 'result':'norm elaboration errors; not accepted'},
        {'file':'Check03.lean', 'exitCode':0, 'result':'permitted dependencies; one unused section instance warning, fixed in Check04'},
        {'file':'Check04.lean', 'exitCode':0, 'result':'final accepted builder check; no diagnostics'},
    ],
}
(root / 'CHECKS.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'axioms'}, indent=2))
