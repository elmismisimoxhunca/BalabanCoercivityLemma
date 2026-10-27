#!/usr/bin/env python3
"""Independent read-only source/dependency checks; output stays beside this script."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[4]
d = root / 'AHP/round3/s1-proper/r1-refute'
pin = root / 'AHP/round3/s1-proper/pin/Statement.lean'
source = d / 'Attempt.lean'
copy = d / 'Attempt.verify.lean'
s = source.read_text()
v = copy.read_text()
p = pin.read_text()

# Preserve all character content other than whitespace for the requested test.
# The full shared context/declaration/check block also matches exactly in bytes.
def norm(t):
    return re.sub(r'\s+', '', t)
start = 'set_option autoImplicit false'
end = '#print axioms GoalNeg1'
pblock = p[p.index(start):p.index(end) + len(end)]
vblock = v[v.index(start):v.index(end) + len(end)]
names = re.findall(r'^def (\w+)', p, re.M)
def extract(t, name):
    begin = re.search(r'^def ' + re.escape(name) + r'\b', t, re.M).start()
    tail = t[begin:]
    # All ten pinned definitions terminate at the next blank line.
    return tail.split('\n\n', 1)[0]
checks = {name: norm(extract(p, name)) == norm(extract(v, name)) for name in names}
round2 = (root / 'AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean').read_text()
helper_start = 'theorem four_touch_cubeBond_of_transverse'
helper_end = '  exact ⟨sites, j, hc, fun e h => Or.inl (he e h).1⟩'
def helpers(t):
    a = t.index(helper_start)
    b = t.index(helper_end, a) + len(helper_end)
    return t[a:b]

# Stronger than an operative-token scan: forbidden whole words absent even in comments.
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', v)
imports = re.findall(r'^import (\S+)\s*$', v, re.M)
local_names = re.findall(r'^(?:def|theorem) ([\w\u0080-\uffff]+)', v, re.M)
printed = re.findall(r'^#print axioms (\S+)', v, re.M)
log_path = d / 'Attempt.verify.lean.log'
exit_path = d / 'Attempt.verify.lean.exit'
log = log_path.read_text() if log_path.exists() else ''
records = re.findall(r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [(n, a) for n, a in records if not {x.strip() for x in a.split(',') if x.strip()} <= allowed]
main = 'Round3.S1Proper.goalNeg1_proved'
main_records = [(n, a) for n, a in records if n == main]
exitcode = int(exit_path.read_text()) if exit_path.exists() else None
hashes = {str(f.relative_to(root)): hashlib.sha256(f.read_bytes()).hexdigest() for f in [source, copy, pin, log_path] if f.exists()}
report = {
    'sourceCopyByteIdentical': source.read_bytes() == copy.read_bytes(),
    'pinnedBlockByteIdentical': pblock == vblock,
    'definitionCount': len(names), 'definitionsWhitespaceNormalized': checks,
    'round2CoverageHelperBlockByteIdentical': helpers(v) == helpers(round2),
    'mainDeclarationExactHeader': bool(re.search(r'^theorem goalNeg1_proved : GoalNeg1 := by$', v, re.M)),
    'namespace': re.findall(r'^namespace (.*)$', v, re.M),
    'variableCommands': re.findall(r'^variable.*$', v, re.M),
    'imports': imports,
    'importsResolveToFrozenSources': all((root / 'lean/src' / (i.replace('.', '/') + '.lean')).is_file() for i in imports),
    'forbiddenTokensEvenInComments': forbidden,
    'localDeclarations': local_names,
    'allLocalDeclarationsHavePrintCommands': all(n in printed for n in local_names),
    'printCommandCount': len(printed), 'dependencyRecordCount': len(records),
    'allPrintCommandsHaveDependencyRecords': all(any(full == n or full.endswith('.' + n) for full, _ in records) for n in printed),
    'nonstandardDependencyRecords': bad, 'mainDependencyRecords': main_records,
    'compilerErrorsOrWarnings': re.findall(r'^.*(?:error:|warning:).*$', log, re.M),
    'exitCode': exitcode, 'sha256': hashes,
}
report['pass'] = all([
    report['sourceCopyByteIdentical'], report['pinnedBlockByteIdentical'],
    len(names) == 10, all(checks.values()), report['round2CoverageHelperBlockByteIdentical'],
    report['mainDeclarationExactHeader'], report['namespace'] == ['Round3.S1Proper'],
    report['variableCommands'] == ['variable {L : PeriodicLatticeExtent}'],
    report['importsResolveToFrozenSources'], not forbidden,
    report['allLocalDeclarationsHavePrintCommands'], report['allPrintCommandsHaveDependencyRecords'],
    len(records) == len(printed), len(main_records) == 1, not bad,
    not report['compilerErrorsOrWarnings'], exitcode == 0,
])
(d / 'Attempt.verify.audit.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report['pass'] else 1)
