"""Independent static/source and fresh-log audit; not numerical evidence."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[4]
here = Path(__file__).resolve().parent
attempt_path = here / 'Attempt.lean'
pin_path = here.parent / 'pin/Statement.lean'
source = attempt_path.read_text()
pin = pin_path.read_text()
stage = (root / 'AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean').read_text()
connectivity = (root / 'lean/src/CvN4.lean').read_text()

def declaration(text, name):
    # All audited declarations start at column zero. Stop before a following
    # column-zero command/comment; preserve every character of the declaration.
    start = re.search(r'^(?:def|theorem) ' + re.escape(name) + r'(?=\s|\{|\()', text, re.M)
    assert start, name
    rest = text[start.start():]
    end = re.search(r'\n(?=(?:/\*|/\-|def |theorem |open |#|end |namespace |variable |set_option ))', rest)
    return (rest[:end.start()] if end else rest).rstrip()

def compare(text, names):
    result = {}
    for name in names:
        a, b = declaration(text, name), declaration(source, name)
        result[name] = {'exact': a == b,
                        'whitespaceNormalized': re.sub(r'\s+', '', a) == re.sub(r'\s+', '', b)}
        assert result[name]['whitespaceNormalized'], name
    return result

pin_names = re.findall(r'^def (\S+)', pin, re.M)
pin_checks = compare(pin, pin_names)
assert len(pin_checks) == 14
stage_names = ['TouchBond', 'CoversPlaqFour', 'plaqCorner', 'CoversPlaqCorner',
               'CurlReadsTouch', 'PerCubeRegularTouch', 'ClassCoupledFour', 'ClassCoupledCorner',
               'cornerA', 'cornerB', 'cornerC', 'cornerD', 'TouchBond.endpoints',
               'coord_shift_ne', 'cornerD_comm', 'mem_siteBox_iff', 'boundary_is_square',
               'edgeAB_mem', 'edgeBD_mem', 'edgeCD_mem', 'edgeAC_mem', 'square_edges_touch',
               'siteBox_fill_of_diagonal', 'siteBox_fill_of_antidiagonal',
               'opposite_of_touch', 'touchCover_all_corners']
stage_checks = compare(stage, stage_names)
frozen_checks = compare(connectivity, ['shift_iter', 'forall_of_shift'])

ns = 'AdalyFormal.AHP.Round2.S2Nonvacuity.'
log = (here / 'Attempt.verify.log').read_text()
records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))", log, re.S)
axioms = {name: [x.strip() for x in deps.split(',') if x.strip()] for name, deps, empty in records}
allow = {'propext', 'Classical.choice', 'Quot.sound'}
assert len(records) == 48 == len(axioms)
assert all(set(xs) <= allow for xs in axioms.values())
local = re.findall(r'^(?:def|theorem) (\S+)', source, re.M)
assert len(local) == 45
assert all(ns + n in axioms for n in local)
prints = re.findall(r'^#print axioms (\S+)', source, re.M)
assert len(prints) == 48
assert all((n if n.startswith('AdalyFormal.') else ns + n) in axioms for n in prints)
assert ns + 'goalNeg2_proved : GoalNeg2\n' in log
assert re.search(r'^theorem goalNeg2_proved : GoalNeg2 := by$', source, re.M)
assert re.findall(r'^namespace (.*)$', source, re.M) == [ns[:-1]]
assert not re.search(r'^(?:notation|local notation|macro|syntax|elab|attribute|instance)\b', source, re.M)
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source)
assert not forbidden
imports = re.findall(r'^import (.*)$', source, re.M)
assert imports == ['ZT5A', 'ZR8Class']
assert all((root / 'lean/src' / (n + '.lean')).is_file() for n in imports)
exit_code = int((here / 'Attempt.verify.exit').read_text())
assert exit_code == 0
assert not re.search(r'\b(?:warning|error):', log)
result = {
    'attemptSHA256': hashlib.sha256(source.encode()).hexdigest(),
    'pinSHA256': hashlib.sha256(pin.encode()).hexdigest(),
    'freshLogSHA256': hashlib.sha256(log.encode()).hexdigest(),
    'recompiledExit': exit_code,
    'pinDefinitions': pin_checks,
    'stageBCopies': stage_checks,
    'frozenConnectivityCopies': frozen_checks,
    'mainDeclaration': ns + 'goalNeg2_proved',
    'mainType': ns + 'GoalNeg2',
    'localDeclarations': len(local),
    'axiomRecordCount': len(records),
    'axioms': axioms,
    'forbiddenTokensFullSource': forbidden,
    'imports': imports,
    'verdict': 'closes-goal',
    'scope': 'GoalNeg2 only; not the four-bond branch or the complete item.'
}
print(json.dumps(result, indent=2, ensure_ascii=False))
