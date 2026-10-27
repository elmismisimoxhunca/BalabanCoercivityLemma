#!/usr/bin/env python3
"""Artifact audit. Never relaunch a compiler or fabricate a wrapper exit file."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
prior = root.parent/'structural-r1'
src_path = root/'Attempt.lean'
src = src_path.read_text()
pin_path = Path('AHP/round3/guarded/pin/Statement.lean')
pin = pin_path.read_bytes()
assert src_path.read_bytes().startswith(pin)
assert src_path.read_bytes() == (prior/'Attempt.lean').read_bytes()
assert src_path.read_bytes().startswith(Path('AHP/round4/guarded/decay-r1/Attempt.lean').read_bytes())
imports = re.findall(r'^import\s+(.*)$', src, re.M)
assert imports == ['DrEquiv']
forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', src)
assert not forbidden
for name in ['GoalPos1','GoalPos2','GoalNeg1','GoalNeg2']:
    assert len(re.findall(r'^def '+name+r'\b',src,re.M)) == 1
stack, declarations = [], []
for line in src.splitlines():
    m = re.fullmatch(r'namespace (\S+)\s*',line)
    if m:
        stack.append(('namespace',m.group(1)));continue
    m = re.fullmatch(r'section(?: (\S+))?\s*',line)
    if m:
        stack.append(('section',m.group(1)));continue
    m = re.fullmatch(r'end(?: (\S+))?\s*',line)
    if m:
        kind,name=stack.pop()
        assert m.group(1) is None or m.group(1)==name
        continue
    m = re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma) (\S+)',line)
    if m:
        declarations.append('.'.join([name for kind,name in stack if kind=='namespace']+[m.group(1)]))
assert not stack
assert len(declarations)==len(set(declarations))==86
assert len(re.findall(r'^#print axioms ',src,re.M))==len(declarations)
# The ONLY accepted compilation evidence is the prior identical source's log.
log=(prior/'Attempt.lean.log').read_text()
assert (prior/'Attempt.lean.exit').read_text().strip()=='0'
assert not re.search(r'\b(error|warning)(?:\(|:)',log)
records={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log):
    deps=sorted(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
    assert set(deps)<={'propext','Classical.choice','Quot.sound'}
    assert m.group(1) not in records
    records[m.group(1)]=deps
assert set(records)==set(declarations)
assert (prior/'Attempt.lean').stat().st_mtime_ns <= (prior/'Attempt.lean.log').stat().st_mtime_ns <= (prior/'Attempt.lean.exit').stat().st_mtime_ns
fresh_exit=root/'Attempt.lean.exit'
fresh_code=int(fresh_exit.read_text()) if fresh_exit.exists() else None
assert fresh_code is None, 'Reassess fresh compile evidence; do not silently reuse the timeout status.'
assert (root/'Attempt.lean.log').read_bytes()==b''
num=json.loads((root/'numerics/sparse_R18_results.json').read_text())
check=json.loads((root/'numerics/sparse_small_check.json').read_text())
assert num['R']==18 and num['room'] and num['epsilon']==1/7680
assert num['physical_fine_sides']==[232,8,8]
assert num['carrier_dimension']==8076
assert len(num['sectors'])==16
assert {tuple(s['sector']) for s in num['sectors']}=={(y,z) for y in range(4) for z in range(4)}
assert sum(s['carrier_dimension'] for s in num['sectors'])==129216
assert all(s['carrier_Schur_min']>0 and s['local_augmented_min_abs_LU_pivot']>1e-8 and
           s['local_inverse_relative_residual']<1e-10 for s in num['sectors'])
assert num['crossing_J_norm_lower_bound']>4e-12
rows=num['rows']
assert rows[-1]['observed_transfer_lower_bound']>10000*rows[0]['observed_transfer_lower_bound']
assert max(r['schur_vs_direct_relative_error'] for r in rows)<1e-5
assert check['B_apply_error']<1e-10 and check['W_apply_error']<1e-10
assert check['qtop_error']<1e-10 and check['pure_row_error']<1e-12
assert all(c['lowest_six_error']<1e-10 for c in check['complex_sector_checks'])
assert max(num['peak_rss_kib'],check['peak_rss_kib'])*1024<2_000_000_000
assert num['address_space_limit_bytes']==check['address_space_limit_bytes']==1900*1024**2<2_000_000_000
for f in ['sparse_small_check','sparse_R18']:
    assert (root/f'numerics/{f}.exit').read_text().strip()=='0'
assert (root/'numerics/sparse_R18_first.exit').read_text().strip()=='1'
helpers={}
for name in ['assembly.py','delta_ops.py','wide_probe.py','observe.py','lift_probe.py','corrected_probe.py']:
    content=(root/'numerics'/name).read_bytes()
    assert content==(prior/'numerics'/name).read_bytes()
    helpers[name]=hashlib.sha256(content).hexdigest()
main='AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed'
result=dict(status='numerical-obstacle; prior-identical-source-compiled; fresh-compile-interrupted',closedGoal='none',
    file=str(src_path.relative_to(Path.cwd())),sourceSha256=hashlib.sha256(src_path.read_bytes()).hexdigest(),
    pinSha256=hashlib.sha256(pin).hexdigest(),pinExactBytePrefix=True,priorExactByteCopy=True,
    imports=imports,forbiddenTokens=forbidden,localDeclarationCount=len(declarations),
    mainDeclaration=main,priorAxiomRecordCount=len(records),priorAxioms=records,
    priorCompiledFile=str((prior/'Attempt.lean').relative_to(Path.cwd())),priorCompileExit=0,
    freshCompilation=dict(command='AHP/round3/lean1.sh AHP/round5/guarded/structural-r2/Attempt.lean',
       status='bash timed out at 200 seconds; repeated exit-file checks absent, no surviving process; not relaunched',
       exitFileExists=False,wrapperExitCode=None,resultSchemaExitCode=-1,
       note='-1 is an unavailable-exit sentinel, not an observed wrapper exit. No log or exit was fabricated.'),
    numericalStatus='floating-point only; lower bound from a sub-observation, not exact proof of divergence or singularity',
    observedTransferLowerBounds=[r['observed_transfer_lower_bound'] for r in rows],
    radius=18,room=True,crossing=num['carrier_crossing'],
    crossingObservedNormLowerBound=num['crossing_J_norm_lower_bound'],
    allSectorDiagnostic='16 localized sparse LU factorizations and positive carrier Schur spectra; not full carrier eigenvalues',
    fullCarrierDimension=129216,peakRSSKiB=max(num['peak_rss_kib'],check['peak_rss_kib']),
    helperSha256=helpers,sourceHashes={name:hashlib.sha256((root/'numerics'/name).read_bytes()).hexdigest()
      for name in ['sparse_probe.py','sparse_small_check.json','sparse_R18_results.json']},
    firstNumericalFailure='ARPACK nonconvergence in sector (0,1); retained first log/exit/results. Final run uses LU unit diagnostics for nonzero sectors, not an uncomputed eigenvalue.')
(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='priorAxioms'},indent=2))
