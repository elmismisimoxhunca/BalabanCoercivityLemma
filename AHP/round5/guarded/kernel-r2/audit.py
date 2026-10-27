#!/usr/bin/env python3
"""Audit actual successful wrapper runs; never manufacture compiler evidence."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b'
MAIN = 'AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation'

def digest(b):
    return hashlib.sha256(b).hexdigest()

def no_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i:i+2] == '/-':
            depth += 1
            out.append('  ')
            i += 2
        elif depth and s[i:i+2] == '-/':
            depth -= 1
            out.append('  ')
            i += 2
        elif not depth and s[i:i+2] == '--':
            end = s.find('\n', i)
            if end == -1:
                break
            out.append(' ' * (end-i))
            i = end
        else:
            out.append(s[i] if not depth or s[i] == '\n' else ' ')
            i += 1
    assert depth == 0
    return ''.join(out)

def declarations(s):
    scopes, result = [], []
    for line in no_comments(s).splitlines():
        m = re.match(r'^namespace\s+([^\s]+)', line)
        if m:
            scopes.append(('namespace', m[1]))
            continue
        if re.match(r'^section(?:\s|$)', line):
            scopes.append(('section', ''))
            continue
        if re.match(r'^end(?:\s|$)', line):
            assert scopes, line
            scopes.pop()
            continue
        m = re.match(r'^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure)\s+([^\s(:]+)', line)
        if m:
            ns = [v for k, v in scopes if k == 'namespace']
            result.append('.'.join(ns + [m[1]]))
    assert not scopes, scopes
    assert len(result) == len(set(result)), 'Duplicate declaration names'
    return result

pin = (ROOT / 'AHP/round3/guarded/pin/Statement.lean').read_bytes()
old = (ROOT / 'AHP/round5/guarded/kernel-r1/KernelDraft.lean').read_bytes()
refute = (ROOT / 'AHP/round4/guarded/refute-r1/Attempt.lean').read_bytes()
final = (HERE / 'Attempt.lean').read_bytes()
inherited = (HERE / 'Inherited.lean').read_bytes()
assert inherited == old
assert inherited.startswith(refute)
assert final.startswith(inherited)
assert final.startswith(pin)

runs = []
for stem in ['Inherited.lean', 'Attempt.lean']:
    source = HERE / stem
    logpath = HERE / (stem + '.log')
    exitpath = HERE / (stem + '.exit')
    text = source.read_text()
    log = logpath.read_text()
    assert exitpath.read_text().strip() == '0', stem
    assert source.stat().st_mtime_ns <= logpath.stat().st_mtime_ns <= exitpath.stat().st_mtime_ns, stem
    assert not re.search(r'\b(?:error|warning)(?:\([^\n]*\))?:', log), stem
    assert not re.search(FORBIDDEN, text), stem
    imports = re.findall(r'^import\s+(.+)$', text, re.M)
    assert imports == ['DrEquiv'], imports
    records = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log, re.S)
    assert records
    deps = {}
    for name, axioms in records:
        actual = {x.strip() for x in axioms.split(',') if x.strip()}
        assert actual <= ALLOWED, (name, actual)
        deps[name] = sorted(actual)
    local = declarations(text)
    missing = sorted(set(local) - set(deps))
    assert not missing, missing
    runs.append({
        'file': str(source.relative_to(ROOT)),
        'command': 'AHP/round3/lean1.sh ' + str(source.relative_to(ROOT)),
        'exitCode': 0,
        'sha256': digest(source.read_bytes()),
        'sourceLogExitOrder': True,
        'imports': imports,
        'localDeclarations': len(local),
        'dependencyRecords': len(records),
        'allLocalDeclarationsPrinted': True,
        'allDependenciesPermitted': True,
        'diagnostics': [],
        'forbiddenTokens': [],
    })
    if stem == 'Attempt.lean':
        assert MAIN in deps
        main_deps = deps[MAIN]

report = {
    'closedGoal': 'none',
    'finalPathFreshlyCompiled': True,
    'pinSHA256': digest(pin),
    'pinExactPrefix': True,
    'inheritedDraftExactCopy': True,
    'round4RefuteExactPrefix': True,
    'inheritedModelsRecompiledAsPartOfInherited': True,
    'mainDeclaration': MAIN,
    'mainAxioms': main_deps,
    'mainScope': 'Conditional actual-carrier Schur separation; lattice realization NOT proved.',
    'newLocalDeclarations': runs[1]['localDeclarations'] - runs[0]['localDeclarations'],
    'runs': runs,
}
(HERE / 'CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
