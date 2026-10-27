#!/usr/bin/env python3
"""Artifact/fidelity audit. No numerical model, and no compilation-success inference."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = HERE / 'Attempt.lean'
LOG = HERE / 'Attempt.lean.log'
EXIT = HERE / 'Attempt.lean.exit'
PRIOR = ROOT / 'AHP/round6/closedform-r1/Attempt.lean'
PIN = ROOT / 'AHP/round3/guarded/pin/Statement.lean'
BRIDGE = ROOT / 'AHP/round5/guarded/ivt-r2/Attempt.lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MAIN = 'AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry'


def records(text):
    return [(name, {x.strip() for x in raw.split(',') if x.strip()})
            for name, raw in re.findall(
                r"^'([^\n]+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                text, re.M)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


source = SRC.read_text()
assert SRC.read_bytes().startswith(PIN.read_bytes())
assert SRC.read_bytes().startswith(BRIDGE.read_bytes())
assert SRC.read_bytes().startswith(PRIOR.read_bytes())
assert re.findall(r'^import (.+)$', source, re.M) == ['DrEquiv']
assert not re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source)
prior_log = Path(str(PRIOR) + '.log')
prior_exit = Path(str(PRIOR) + '.exit')
assert prior_exit.read_text().strip() == '0'
old_records = dict(records(prior_log.read_text()))
assert MAIN in old_records
assert all(deps <= ALLOWED for deps in old_records.values())
assert not re.search(r'\b(?:error|warning)(?:\([^\n]*?\))?:', prior_log.read_text())
log = LOG.read_text()
current_records = records(log)
errors = len(re.findall(r': error(?:\([^\n]*?\))?:', log))
warnings = len(re.findall(r': warning(?:\([^\n]*?\))?:', log))
new_records = [(name, sorted(deps)) for name, deps in current_records
               if '.ClosedFormR2.' in name]
result = {
    'closedGoal': 'none',
    'file': str(SRC.relative_to(ROOT)),
    'freshCompilationSucceeded': False,
    'wrapperBashTimeoutSeconds': 1200,
    'exitFilePresent': EXIT.exists(),
    'recordedExitCode': int(EXIT.read_text().strip()) if EXIT.exists() else None,
    'reportedExitCode': int(EXIT.read_text().strip()) if EXIT.exists() else -1,
    'reportedExitMeaning': '-1 means missing wrapper exit, not an observed Lean exit code',
    'logErrorCount': errors,
    'logWarningCount': warnings,
    'newDependencyRecords': new_records,
    'newVerifiedResultClaimed': False,
    'mainDeclaration': MAIN,
    'mainLine': 2643,
    'mainEvidenceStatus': 'prior pass compilation only; inherited unchanged',
    'mainAxioms': sorted(old_records[MAIN]),
    'priorSource': str(PRIOR.relative_to(ROOT)),
    'priorExitCode': 0,
    'priorSourceSha256': sha(PRIOR),
    'priorLogSha256': sha(prior_log),
    'pinVerbatimBytePrefix': True,
    'round5BridgeVerbatimBytePrefix': True,
    'round6Pass1VerbatimBytePrefix': True,
    'imports': ['DrEquiv'],
    'forbiddenSourceTokens': [],
    'sourceSha256': sha(SRC),
    'logSha256': sha(LOG),
    'pinSha256': sha(PIN),
    'round5BridgeSha256': sha(BRIDGE),
    'completeCurrentDependencyRecordCount': len(current_records),
    'completeCurrentRecordsUseAllowedAxioms': all(deps <= ALLOWED for _, deps in current_records),
    'completeCurrentRecordsDoNotProveFileSuccess': True,
    'numericalJobsRun': 0,
    'timedOutInvocationRelaunched': False,
}
(HERE / 'CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
