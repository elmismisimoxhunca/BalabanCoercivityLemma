#!/usr/bin/env python3
"""Static source/evidence audit. Never interprets missing exits as compilation."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
track = root.parent
pin = (track / 'pin/Statement.lean').read_bytes()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
forbidden = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def deps(path):
    if not path.exists():
        return []
    text = path.read_text()
    return [(m.group(1), [s.strip() for s in m.group(2).split(',') if s.strip()])
            for m in re.finditer(r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", text)]

def source_audit(path):
    data = path.read_bytes()
    text = data.decode()
    imported = re.findall(r'^import (.+)$', text, re.M)
    declarations = re.findall(r'^(?:noncomputable )?(?:def|abbrev|theorem) ([\w\']+)', text, re.M)
    printed = re.findall(r'^#print axioms ([\w\']+)', text, re.M)
    logfile, exitfile = Path(str(path)+'.log'), Path(str(path)+'.exit')
    records = deps(logfile)
    return {
        'sha256': sha(data),
        'pinPrefixVerbatim': data.startswith(pin),
        'imports': imported,
        'frozenOnlyImports': all((track.parents[2]/'lean/src'/Path(i.replace('.', '/')+'.lean')).is_file() for i in imported),
        'declaredCount': len(declarations),
        'printCount': len(printed),
        'missingPrints': sorted(set(declarations)-set(printed)),
        'rawForbiddenTokens': forbidden.findall(text),
        'exit': exitfile.read_text().strip() if exitfile.exists() else None,
        'logBytes': logfile.stat().st_size if logfile.exists() else None,
        'dependencyRecords': len(records),
        'disallowedDependencies': [(n,a) for n,a in records if set(a)-allowed],
    }

files = {p.name: source_audit(p) for p in sorted(root.glob('*.lean'))}
partial = track/'attempt/Partial.lean'
replay = track/'verify/Partial.lean'
old_records = deps(Path(str(partial)+'.log'))
replay_records = deps(Path(str(replay)+'.log'))
main = 'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class'
original = partial.read_bytes()
old_body = original[original.index(b'/-!'):]
report = {
    'status': 'open',
    'closedGoal': 'none',
    'finalAssemblyCompiled': False,
    'pinSHA256': sha(pin),
    'files': files,
    'finalContainsPriorPartialVerbatimExceptImports': old_body in (root/'Attempt.lean').read_bytes(),
    'priorCompiledPartial': {
        'file': str(partial.relative_to(track.parents[2])),
        'sourceSHA256': sha(original),
        'replayByteIdentical': original == replay.read_bytes(),
        'exit': Path(str(partial)+'.exit').read_text().strip(),
        'replayExit': Path(str(replay)+'.exit').read_text().strip(),
        'dependencyRecords': len(old_records),
        'replayDependencyRecords': len(replay_records),
        'disallowedDependencies': [(n,a) for n,a in old_records+replay_records if set(a)-allowed],
        'main': main,
        'mainDependencies': [a for n,a in old_records if n==main],
        'replayMainDependencies': [a for n,a in replay_records if n==main],
    },
    'limitations': 'No r2 source has a successful wrapper exit. Static checks certify neither elaboration nor proof. Prior compiled partial is prior evidence only.'
}
assert all(v['pinPrefixVerbatim'] and v['frozenOnlyImports'] and not v['missingPrints'] and not v['rawForbiddenTokens'] for v in files.values())
assert report['finalContainsPriorPartialVerbatimExceptImports']
assert report['priorCompiledPartial']['replayByteIdentical']
assert report['priorCompiledPartial']['exit'] == report['priorCompiledPartial']['replayExit'] == '0'
assert not report['priorCompiledPartial']['disallowedDependencies']
(root/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
