#!/usr/bin/env python3
"""Audit this track's final sources and retained compiler evidence."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
pin = root.parent / 'pin' / 'Statement.lean'
source = root / 'Attempt.lean'
s = source.read_text()
p = pin.read_bytes()
assert source.read_bytes().count(p) == 1, 'pin not embedded verbatim exactly once'
assert (root / 'Attempt.verify.lean').read_bytes() == source.read_bytes()

# Strip nested Lean block comments and line comments before checking source tokens.
def code_only(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return ''.join(out)

code = code_only(s)
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', code)
assert not forbidden, forbidden
declarations = re.findall(r'^\s*(?:noncomputable\s+)?(?:private\s+)?(?:theorem|lemma|def|abbrev|structure)\s+([^\s(:{]+)', code, re.M)
prints = re.findall(r'^\s*#print axioms\s+(\S+)', code, re.M)
missing = sorted(set(declarations) - set(prints))
assert not missing, missing
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
logs = []
for name in ['Attempt.lean', 'Attempt.verify.lean']:
    exit_code = int((root / (name + '.exit')).read_text().strip())
    log = (root / (name + '.log')).read_text()
    assert exit_code == 0, (name, exit_code)
    assert 'error:' not in log and 'sorryAx' not in log
    deps = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    no_deps = re.findall(r"'([^']+)' does not depend on any axioms", log)
    for decl, ax in deps:
        assert set(x.strip() for x in ax.split(',') if x.strip()) <= allowed, (decl, ax)
    assert len(deps) + len(no_deps) >= len(prints)
    logs.append({'file': name, 'exitCode': exit_code, 'printedDeclarations': len(deps) + len(no_deps),
                 'sha256': hashlib.sha256((root / name).read_bytes()).hexdigest()})
imports = re.findall(r'^import (\S+)', code, re.M)
workspace = root.parents[2]
for mod in imports:
    assert (workspace / 'lean' / 'src' / (mod.replace('.', '/') + '.lean')).exists(), mod
result = {
    'closedGoal': 'none',
    'pinBytes': len(p),
    'pinSha256': hashlib.sha256(p).hexdigest(),
    'pinVerbatimOccurrences': 1,
    'sourceLines': len(s.splitlines()),
    'explicitDeclarations': len(declarations),
    'axiomPrintCommands': len(prints),
    'missingAxiomPrints': missing,
    'forbiddenTokens': forbidden,
    'importsFrozenSourceOnly': imports,
    'allowedAxioms': sorted(allowed),
    'compilations': logs,
    'mainDeclaration': 'Round11.LargeA.base_flat_large_mass_slice',
    'remainingAnalyticInput': 'Round11.LargeA.EventualHalfPositive',
}
(root / 'AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
