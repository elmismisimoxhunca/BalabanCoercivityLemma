#!/usr/bin/env python3
"""Audit final-path Lean evidence. No numerical operator is modeled here."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = HERE / 'Attempt.lean'
LOG = HERE / 'Attempt.lean.log'
EXIT = HERE / 'Attempt.lean.exit'
source = SRC.read_text()
log = LOG.read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(text):
    """Remove nested block/line comments without changing line numbers."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            out.append('  ')
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            out.append('  ')
            i += 2
        elif not depth and text[i:i+2] == '--':
            j = text.find('\n', i)
            if j < 0:
                j = len(text)
            out.append(' ' * (j-i))
            i = j
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    assert depth == 0
    return ''.join(out)


pin = ROOT / 'AHP/round3/guarded/pin/Statement.lean'
bridge = ROOT / 'AHP/round5/guarded/ivt-r2/Attempt.lean'
prior = ROOT / 'AHP/round6/limits-r1/Attempt.lean'
jet = ROOT / 'AHP/round6/limits-r1/JetLemma.lean'
assert SRC.read_bytes().startswith(pin.read_bytes())
assert SRC.read_bytes().startswith(bridge.read_bytes())
assert SRC.read_bytes().startswith(prior.read_bytes())
assert jet.read_bytes() in SRC.read_bytes()
assert re.findall(r'^import (.+)$', source, re.M) == ['DrEquiv']
assert (ROOT / 'lean/src/DrEquiv.lean').exists()
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source)
assert not forbidden
assert EXIT.read_text().strip() == '0'
assert SRC.stat().st_mtime_ns <= LOG.stat().st_mtime_ns <= EXIT.stat().st_mtime_ns
assert not re.search(r': error(?:\(|:)', log)
assert 'sorryAx' not in log

records = re.findall(r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.M)
record_map = {}
for name, raw in records:
    axioms = {a.strip() for a in raw.split(',') if a.strip()}
    assert axioms <= allowed, (name, axioms)
    if name in record_map:
        assert record_map[name] == axioms
    record_map[name] = axioms

stack = []
declarations = {}
prints = []
for line_no, line in enumerate(strip_comments(source).splitlines(), 1):
    m = re.match(r'^(namespace|section)\b\s*(\S*)', line)
    if m:
        stack.append(m.groups())
        continue
    m = re.match(r'^end\b\s*(\S*)', line)
    if m:
        kind, name = stack.pop()
        assert not m[1] or m[1] == name, (line_no, name, m[1])
        continue
    ns = '.'.join(name for kind, name in stack if kind == 'namespace')
    m = re.match(r"^(?:noncomputable )?(?:abbrev|def|theorem|lemma|instance)\s+([\w.']+)", line)
    if m:
        name = ns + '.' + m[1] if ns else m[1]
        assert name not in declarations, name
        declarations[name] = line_no
    m = re.match(r"^#print axioms ([\w.']+)", line)
    if m:
        name = m[1]
        candidates = [name, ns + '.' + name]
        matched = [n for n in candidates if n in record_map]
        assert matched, (line_no, name)
        prints.append(matched[0])
assert not stack
assert set(declarations) <= set(prints), set(declarations) - set(prints)
assert set(prints) == set(record_map), set(record_map) - set(prints)

main = 'AdalyFormal.Round6.Guarded.LimitsR2.twistD_kills_interiorInvisible'
main_line = "'" + main + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert record_map[main] == allowed
result = {
    'closedGoal': 'none',
    'exitCode': 0,
    'sourceSha256': sha(SRC),
    'logSha256': sha(LOG),
    'exitSha256': sha(EXIT),
    'pinVerbatimBytePrefix': True,
    'round5BridgeVerbatimBytePrefix': True,
    'round6Pass1VerbatimBytePrefix': True,
    'polarizationHelperVerbatim': True,
    'imports': ['DrEquiv'],
    'forbiddenTokens': forbidden,
    'localDeclarationCount': len(declarations),
    'dependencyRecordCount': len(records),
    'everyLocalDeclarationHasMatchedPermittedRecord': True,
    'allDependencyRecordsPermitted': True,
    'sourceLogExitTimestampOrder': True,
    'warnings': [line for line in log.splitlines() if ': warning:' in line],
    'mainDeclaration': main,
    'mainDeclarationLine': declarations[main],
    'axiomLine': main_line,
    'round6Declarations': {n: line for n, line in declarations.items() if line > len(bridge.read_text().splitlines())},
    'numericalJobsRun': 0,
    'scope': 'Fresh final compilation and complete axiom audit. No positive-amplitude crossing-kernel sign, cofinal obstruction, or pinned-goal closure is claimed.'
}
(HERE / 'CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
