from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
source = root / 'Attempt.lean'
checked = root / 'Check3.lean'
pin = root.parents[2] / 'round3' / 'guarded' / 'pin' / 'Statement.lean'
# root is AHP/round4/guarded/gap-r1; parents[2] is AHP.
text = source.read_text()
log_path = Path(str(checked) + '.log')
exit_path = Path(str(checked) + '.exit')
log = log_path.read_text()
records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
records += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
violations = {
    name: sorted(set(filter(None, map(str.strip, deps.split(',')))) - allowed)
    for name, deps in records
    if set(filter(None, map(str.strip, deps.split(',')))) - allowed
}
local_declarations = re.findall(r'^(?:theorem|def|abbrev|noncomputable def)\s+(\w+)', text, re.M)
printed = {name.rsplit('.', 1)[-1] for name, _ in records}
missing = sorted(set(local_declarations) - printed)
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
imports = re.findall(r'^import\s+(.+)$', text, re.M)
new_records = [(name, deps) for name, deps in records if '.Round4.Guarded.GapR1.' in name]
errors = re.findall(r'^.*(?:error|warning)(?:\(|:).*$', log, re.M)
checks = {
    'source': str(source),
    'compiledCopy': str(checked),
    'compileCommand': 'AHP/round3/lean1.sh AHP/round4/guarded/gap-r1/Check3.lean',
    'exitCode': int(exit_path.read_text().strip()),
    'pinBytePrefix': source.read_bytes().startswith(pin.read_bytes()),
    'identicalToCompiledCopy': source.read_bytes() == checked.read_bytes(),
    'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'pinSha256': hashlib.sha256(pin.read_bytes()).hexdigest(),
    'imports': imports,
    'forbiddenTokens': forbidden,
    'dependencyRecordCount': len(records),
    'newDependencyRecordCount': len(new_records),
    'disallowedDependencies': violations,
    'unprintedLocalDeclarations': missing,
    'diagnostics': errors,
    'compiledSourceMtimeNs': checked.stat().st_mtime_ns,
    'logMtimeNs': log_path.stat().st_mtime_ns,
    'exitMtimeNs': exit_path.stat().st_mtime_ns,
    'newDependencyRecords': [
        "'" + name + "' depends on axioms: [" + ', '.join(map(str.strip, deps.split(','))) + "]"
        for name, deps in new_records
    ],
    'closure': 'none',
    'initialAttemptWrapper': 'No exit record, empty log, no surviving process; not relaunched.',
}
assert checks['exitCode'] == 0
assert checks['pinBytePrefix'] and checks['identicalToCompiledCopy']
assert imports == ['DrEquiv']
assert not forbidden and not violations and not missing and not errors
assert len(records) == 54 and len(new_records) == 12
assert checked.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
(root / 'CHECKS.json').write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps({k: checks[k] for k in ['exitCode', 'pinBytePrefix', 'identicalToCompiledCopy',
    'dependencyRecordCount', 'newDependencyRecordCount', 'closure', 'sourceSha256']}, indent=2))
