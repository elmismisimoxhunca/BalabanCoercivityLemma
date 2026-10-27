#!/usr/bin/env python3
"""Check pin identity, local declaration prints, compile result and source safety."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[4]
work = Path(__file__).resolve().parent
src = (work / 'Attempt.lean').read_text()
pin = (root / 'AHP/round2/s2-nonvacuity/pin/Statement.lean').read_text()
stage = (root / 'AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean').read_text()
frozen = (root / 'lean/src/CvN4.lean').read_text()
log = (work / 'Attempt.lean.log').read_text()
ns = 'AdalyFormal.AHP.Round2.S2Nonvacuity.'


def declaration(text, kind, name):
    start = re.search(r'^' + kind + r' ' + re.escape(name) + r'(?=[\s({])', text, re.M).start()
    end = text.find('\n\n', start)
    return text[start:end if end >= 0 else len(text)]


pinned = re.findall(r'^def ([^\s({]+)', pin, re.M)
assert len(pinned) == 14
for name in pinned:
    assert declaration(src, 'def', name) == declaration(pin, 'def', name), name
for name in ('cornerA', 'cornerB', 'cornerC', 'cornerD'):
    assert declaration(src, 'def', name) == declaration(stage, 'def', name), name
for name in ('shift_iter', 'forall_of_shift'):
    assert declaration(src, 'theorem', name) == declaration(frozen, 'theorem', name), name
assert re.findall(r'^import (\S+)', src, re.M) == ['ZT5A', 'ZR8Class']
assert (work / 'Attempt.lean.exit').read_text().strip() == '0'
assert 'error:' not in log and 'error(' not in log and 'warning:' not in log
forbidden = r'\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b'
assert not re.search(forbidden, src), 'forbidden source token'
assert not re.search(r'\bsorryAx\b', log)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log):
    values = {x.strip() for x in (m[2] or '').split(',') if x.strip()}
    assert values <= allowed, (m[1], values)
    records[m[1]] = sorted(values)
local = re.findall(r'^(?:def|theorem) ([^\s({]+)', src, re.M)
assert all(ns + name in records for name in local)
assert ns + 'goalNeg2_proved : GoalNeg2' in log
result = {
    'exitCode': 0,
    'sourceSha256': hashlib.sha256(src.encode()).hexdigest(),
    'pinnedDefinitionsVerbatim': pinned,
    'copiedGeometryDefinitionsVerbatim': ['cornerA', 'cornerB', 'cornerC', 'cornerD'],
    'copiedConnectivityTheoremsVerbatim': ['shift_iter', 'forall_of_shift'],
    'localDeclarations': len(local),
    'axiomRecords': len(records),
    'allLocalDeclarationsPrinted': True,
    'axiomListsAllStandard': True,
    'forbiddenSourceTokens': 0,
    'mainType': ns + 'goalNeg2_proved : GoalNeg2',
    'mainAxioms': records[ns + 'goalNeg2_proved'],
    'numericsExitCode': int((work / 'numerics.exit').read_text()),
}
print(json.dumps(result, indent=2))
