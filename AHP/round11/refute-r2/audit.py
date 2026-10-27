#!/usr/bin/env python3
"""Static/check-log audit of the final compiled artifact; no Lean invocation."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
attempt = out / 'Attempt.lean'
pin = root / 'AHP/round11/pin/Statement.lean'
oldpin = root / 'AHP/round7/s1-odd/pin/Statement.lean'
src = attempt.read_text()
log = Path(str(attempt) + '.log').read_text()

# Strip nested Lean block comments and line comments before declaration checks.
def uncomment(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            if not depth or text[i] == '\n':
                result.append(text[i])
            i += 1
    assert depth == 0
    return ''.join(result)

code = uncomment(src)
namespace = []
declarations = []
for line in code.splitlines():
    if m := re.match(r'^namespace\s+(\S+)', line):
        namespace.append(m[1])
    elif re.match(r'^end\b', line):
        namespace.pop()
    elif m := re.match(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|instance)\s+(\S+)', line):
        declarations.append('.'.join(namespace + [m[1]]))
assert not namespace
printed = {}
for name, dependencies in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M):
    printed[name] = [s.strip() for s in dependencies.split(',') if s.strip()]
for name in re.findall(r"^'([^']+)' does not depend on any axioms", log, re.M):
    printed[name] = []
whitelist = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(declarations) == set(printed), (set(declarations)-set(printed), set(printed)-set(declarations))
assert all(set(v) <= whitelist for v in printed.values())
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', code)
assert 'error:' not in log and 'warning:' not in log
assert int(Path(str(attempt) + '.exit').read_text()) == 0
assert int(Path(str(pin) + '.exit').read_text()) == 0
assert pin.read_text() in src
assert pin.read_text().startswith(oldpin.read_text())
assert Path(str(attempt) + '.log').stat().st_mtime >= attempt.stat().st_mtime
imports = re.findall(r'^import (\S+)', code, re.M)
assert imports == ['D1Final', 'GdPlaq', 'D1Lit']
assert all((root / 'lean/src' / (name + '.lean')).is_file() for name in imports)
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
main = 'Round11.RefuteR2.window_sqrt5_closed_proved'
report = {
    'closedGoal': 'none',
    'strongestCompiledTheorem': main,
    'statement': 'For every ell >= 2 and every 0 < a <= 4*sqrt(5), not Round7.S1Odd.P428TouchFourAt ell hell a.',
    'allAClosed': False,
    'largeAClosed': False,
    'attempt': str(attempt.relative_to(root)),
    'pin': str(pin.relative_to(root)),
    'attemptSHA256': sha(attempt),
    'pinSHA256': sha(pin),
    'logSHA256': sha(Path(str(attempt) + '.log')),
    'attemptExit': 0,
    'pinExit': 0,
    'pinVerbatimInAttempt': True,
    'round7PinVerbatimPrefix': True,
    'imports': imports,
    'localDeclarationCount': len(declarations),
    'axiomPrintoutCount': len(printed),
    'axiomWhitelist': sorted(whitelist),
    'allAxiomPrintoutsWhitelisted': True,
    'forbiddenTokensAbsent': True,
    'compilerWarningsAbsent': True,
    'mainAxiomLine': next(line for line in log.splitlines() if line.startswith("'" + main + "'")),
    'obstacle': 'The proved endpoint upper bound is (a-4*sqrt(5))*||v||^2. For a>4*sqrt(5), this witness supplies no nonpositive endpoint direction. No all-a crossing or independent final-form failure has been established.',
    'declarations': printed,
}
(out / 'AUDIT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'declarations'}, indent=2))
