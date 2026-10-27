from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
src_path = root / 'Attempt.lean'
log_path = root / 'Attempt.lean.log'
exit_path = root / 'Attempt.lean.exit'
src, log = src_path.read_text(), log_path.read_text()
pin = Path('AHP/round3/guarded/pin/Statement.lean').read_bytes()
decay1 = Path('AHP/round4/guarded/decay-r1/Attempt.lean').read_bytes()
assert src_path.read_bytes().startswith(pin)
assert src_path.read_bytes().startswith(decay1)
assert exit_path.read_text().strip() == '0'
assert not re.search(r'\b(error|warning)(?:\(|:)', log)
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', src)
assert not forbidden, forbidden
imports = re.findall(r'^import\s+(.*)$', src, re.M)
assert imports == ['DrEquiv']
for n in ['GoalPos1', 'GoalPos2', 'GoalNeg1', 'GoalNeg2']:
    assert len(re.findall(r'^def '+n+r'\b', src, re.M)) == 1
stack, declarations = [], []
for line in src.splitlines():
    m = re.fullmatch(r'namespace (\S+)\s*', line)
    if m:
        stack.append(('namespace', m.group(1))); continue
    m = re.fullmatch(r'section(?: (\S+))?\s*', line)
    if m:
        stack.append(('section', m.group(1))); continue
    m = re.fullmatch(r'end(?: (\S+))?\s*', line)
    if m:
        kind, name = stack.pop()
        assert m.group(1) is None or m.group(1) == name
        continue
    m = re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma) (\S+)', line)
    if m:
        declarations.append('.'.join([name for kind, name in stack if kind == 'namespace']+[m.group(1)]))
assert not stack
assert len(declarations) == len(set(declarations))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log):
    deps = sorted(s.strip() for s in (m.group(2) or '').split(',') if s.strip())
    assert set(deps) <= allowed, (m.group(1), deps)
    assert m.group(1) not in records
    records[m.group(1)] = deps
assert set(records) == set(declarations), (set(declarations)-set(records), set(records)-set(declarations))
assert len(re.findall(r'^#print axioms ', src, re.M)) == len(declarations)
assert src_path.stat().st_mtime_ns <= log_path.stat().st_mtime_ns <= exit_path.stat().st_mtime_ns
# Generic algebra and all definitions in New.lean remain verbatim; only failed
# concrete elaboration proofs were repaired and one specialization helper added.
new = Path('AHP/round4/guarded/decay-r2/New.lean').read_text()
for start, end in [
    ('theorem relativeReturn_apply', '/-- A source-specific bound'),
    ('theorem relativeReturn_norm_le_observed', 'end Algebra'),
    ('noncomputable def observedGuardTransfer', '/-- Exact inverse-relative return'),
    ('def CObservedGuardSmall', '/-- Conditional only:'),
]:
    block = new[new.index(start):new.index(end, new.index(start))].rstrip()
    assert block in src, start
num = json.loads((root/'numerics/observation_results.json').read_text())
lift = json.loads((root/'numerics/lift_checks.json').read_text())
assert num['epsilon'] == 1/7680
assert num['crossing_observed_norm'] > .99
assert num['rows'][-1]['observed_transfer_norm'] > 5e6
assert lift['minimum_carrier_abs_over_all_sectors'] > 1e-8
assert lift['total_sector_dimension'] == lift['full_carrier_dimension'] == 18624
assert all(r['negative_count'] == 0 for r in lift['sectors'])
assert max(num['peak_rss_kib'], lift['peak_rss_kib'])*1024 < 2_000_000_000
# Provenance: helper scripts copied unchanged, never executed through their mains.
helper_hashes = {}
for name in ['assembly.py', 'delta_ops.py', 'wide_probe.py', 'lift_probe.py', 'corrected_probe.py']:
    content=(root/'numerics'/name).read_bytes()
    assert content == (Path('AHP/round3/guarded/r3-refute/numerics')/name).read_bytes()
    helper_hashes[name]=hashlib.sha256(content).hexdigest()
main='AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed'
result = dict(status='compiled-partial-only; numerical obstacle',closedGoal='none',
    file=str(src_path.relative_to(Path.cwd())),exitCode=0,
    compileCommand='AHP/round3/lean1.sh AHP/round5/guarded/structural-r1/Attempt.lean',
    sha256=hashlib.sha256(src_path.read_bytes()).hexdigest(),
    pinSha256=hashlib.sha256(pin).hexdigest(),pinExactBytePrefix=True,
    round4Decay1ExactBytePrefix=True,imports=imports,forbiddenTokens=forbidden,
    localDeclarationCount=len(declarations),axiomRecordCount=len(records),
    axioms=records,mainDeclaration=main,
    numericalStatus='floating-point only, no validated error bounds or exact Fourier dictionary',
    observedTransferNorms=[r['observed_transfer_norm'] for r in num['rows']],
    fullLiftMinSampledAbsEigenvalue=lift['minimum_carrier_abs_over_all_sectors'],
    numericalHelperSha256=helper_hashes,
    preliminaryCompilation='Exit 1 on the initial New.lean copy: concrete elaboration errors. Repaired locally; final wrapper exit 0.')
(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='axioms'},indent=2))
