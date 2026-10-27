#!/usr/bin/env python3
"""Read-only source/log audit; emits its report inside this attempt directory."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
FILE = HERE / 'Attempt.lean'
PIN = HERE.parent / 'pin' / 'Statement.lean'
src = FILE.read_text()
pin = PIN.read_text()
log_path = Path(str(FILE) + '.log')
exit_path = Path(str(FILE) + '.exit')
log = log_path.read_text()
exit_code = int(exit_path.read_text().strip())
NAMES = ['plaqCorner', 'TouchBond', 'CoversPlaqFour', 'CurlReadsTouch',
         'PerCubeRegularTouch', 'ClassCoupledFour', 'selCorner',
         'P428TouchFour', 'GoalPos1', 'GoalNeg1']

def declaration(text, name):
    pattern = r'(?ms)^def ' + re.escape(name) + r'\b.*?(?=\n\s*\n)'
    m = re.search(pattern, text)
    assert m, name
    return m.group(0)

pins = {name: declaration(pin, name) == declaration(src, name) for name in NAMES}
local_declarations = re.findall(r"(?m)^(?:noncomputable\s+)?(?:def|theorem) ([\w.']+)", src)
printed = re.findall(r"(?m)^#print axioms ([\w.']+)", src)
missing_prints = sorted(set(local_declarations) - set(printed))
forbidden = sorted(set(re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', src)))
imports = re.findall(r'(?m)^import (\S+)', src)
imports_frozen = {name: (ROOT / 'lean' / 'src' / (name.replace('.', '/') + '.lean')).is_file()
                  for name in imports}
records = []
for line in log.splitlines():
    if ' depends on axioms: ' in line:
        prefix, values = line.split(' depends on axioms: ', 1)
        names = [x.strip() for x in values.strip('[]').split(',') if x.strip()]
        records.append({'name': prefix.strip("'"), 'axioms': names})
    elif ' does not depend on any axioms' in line:
        records.append({'name': line.split(' does not')[0].strip("'"), 'axioms': []})
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
standard = all(set(r['axioms']) <= allowed for r in records)
missing_records = sorted({'Round3.S1Proper.' + name for name in local_declarations} -
                         {r['name'] for r in records})
main = 'Round3.S1Proper.goalPos1_iff_twoUnits'
main_line = next((line for line in log.splitlines() if line.startswith("'" + main + "' depends")), None)
report = {
    'file': str(FILE.relative_to(ROOT)),
    'sourceSha256': hashlib.sha256(src.encode()).hexdigest(),
    'pinSha256': hashlib.sha256(pin.encode()).hexdigest(),
    'exitCode': exit_code,
    'logNewerThanSource': log_path.stat().st_mtime_ns >= FILE.stat().st_mtime_ns,
    'definitionsVerbatim': pins,
    'importsFrozen': imports_frozen,
    'forbiddenTokensRaw': forbidden,
    'localDeclarationCount': len(local_declarations),
    'missingLocalPrintCommands': missing_prints,
    'axiomRecordCount': len(records),
    'axiomsStandard': standard,
    'missingLocalDependencyRecords': missing_records,
    'compilerErrors': [l for l in log.splitlines() if 'error:' in l],
    'compilerWarnings': [l for l in log.splitlines() if 'warning:' in l],
    'closedGoal': 'none',
    'mainDeclaration': main,
    'axiomLine': main_line,
}
report['pass'] = (exit_code == 0 and report['logNewerThanSource'] and
                  all(pins.values()) and all(imports_frozen.values()) and
                  not forbidden and not missing_prints and not missing_records and
                  standard and bool(main_line) and not report['compilerErrors'])
(HERE / 'AUDIT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(0 if report['pass'] else 1)
