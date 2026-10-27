"""Audit P1 publication, verbatim interfaces, clean exits and all dependency prints."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
local = OUT / 'Trial.lean'
shared = ROOT / 'AHP/round13/shared/trial/R1_Trial.lean'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
required = [
    'patchSite_injective', 'trialBond_injective', 'trialField_norm', 'trialField_mem',
    'trial_higher_rows_zero', 'trial_mass_eq', 'trial_T_zero', 'trial_W_eq',
    'trialPlaq_injective', 'trial_plaq_zero_off', 'trial_delta_sum',
    'trial_holonomy', 'trial_hol_parts', 'trial_atom_values', 'edgeIndex_spec',
    'localQuad_value', 'trial_delta_value', 'trial_curved_energy', 'trial_flat_energy',
    'trial_carrier_energy', 'rightStar_negative_halfpi', 'cofinal_rightStar_negative_halfpi',
]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert local.read_bytes() == shared.read_bytes()
records = []
for source in [local, shared]:
    text = source.read_text()
    assert re.findall(r'^import (.+)$', text, re.M) == ['DrEquiv']
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', text)
    log = Path(str(source) + '.log')
    exit_path = Path(str(source) + '.exit')
    assert exit_path.read_text().strip() == '0'
    logtext = log.read_text()
    assert 'error:' not in logtext and 'sorryAx' not in logtext
    prints = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", logtext)
    assert prints
    for name, ax in prints:
        axioms = {x.strip() for x in ax.split(',') if x.strip()}
        assert axioms <= allowed, (name, axioms)
    table = {name: [x.strip() for x in ax.split(',') if x.strip()] for name, ax in prints}
    for short in required:
        assert 'AdalyFormal.Round13.Trial.' + short in table
    own = [name for name in table if name.startswith('AdalyFormal.Round13.Trial.')]
    assert len(own) == 91, len(own)
    locations = {}
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r'(?:theorem|def|abbrev) (\w+)', line)
        if m and m[1] in required:
            locations[m[1]] = i
    records.append({
        'source': str(source.relative_to(ROOT)), 'source_sha256': sha(source),
        'log_sha256': sha(log), 'exit': 0, 'lines': len(text.splitlines()),
        'printed_records': len(prints), 'new_declarations': len(own),
        'required_theorems': {n: {'line': locations[n], 'axioms': table['AdalyFormal.Round13.Trial.' + n]} for n in required},
    })
copy_checks = []
text = local.read_text()
for copy in json.loads((OUT / 'COPIES.json').read_text()):
    p = ROOT / copy['source']
    assert sha(p) == copy['source_sha256']
    # The destination offset pins the exact fragment, including its original whitespace.
    off = sum(len(line) for line in text.splitlines(keepends=True)[:copy['destination_first_line']-1])
    # Character/UTF-8 lengths differ: use byte offsets for the actual SHA comparison.
    boff = len(text[:off].encode())
    fragment_bytes = text.encode()[boff:boff+copy['fragment_bytes']]
    assert hashlib.sha256(fragment_bytes).hexdigest() == copy['fragment_sha256']
    assert fragment_bytes in p.read_bytes()
    copy_checks.append({'source': copy['source'], 'verified_verbatim': True})
result = {
    'status': 'PASS', 'scope': 'P1 only; not P2, P3, KernelLine, or GoalNeg2',
    'byte_identical': True, 'files': records, 'copies': copy_checks,
    'numerics_used_as_proof': False,
    'qualification': 'Two separate builder executions, not independent mathematical review.',
}
(OUT / 'AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'files': [r['source'] for r in records],
                  'new_declarations': records[0]['new_declarations'], 'standard_axioms_only': True,
                  'copies_verified': len(copy_checks)}, indent=2))
