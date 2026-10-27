#!/usr/bin/env python3
"""Audit this round's compact algebraic proofs, not the unproved operator certificate."""
from pathlib import Path
import hashlib
import json
import re

base = Path(__file__).resolve().parent
root = base.parents[3]
shared = root / 'AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean'
paths = [base / 'PolynomialGrid.lean', base / 'MovingRoot.lean', base / 'SeedObstruction.lean', shared]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
namespace = 'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.'
reports = []
for path in paths:
    source = path.read_text()
    logpath = Path(str(path) + '.log')
    exitpath = Path(str(path) + '.exit')
    log = logpath.read_text()
    decls = re.findall(r'^(?:noncomputable\s+)?(?:def|lemma|theorem|structure)\s+(\w+)', source, re.M)
    raw_records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    records = {n: [x.strip() for x in deps.split(',') if x.strip()] for n, deps in raw_records}
    checks = {
        'exit_zero': exitpath.read_text().strip() == '0',
        'frozen_import_only': re.findall(r'^import (.+)$', source, re.M) == ['D1IVT'],
        'no_prohibited_devices': not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b', source),
        'no_diagnostics': not re.search(r'\b(error|warning):|sorryAx', log),
        'standard_axioms_only': all(set(ds) <= allowed for ds in records.values()),
        'every_declaration_audited': all(namespace + d in records for d in decls),
        'exact_record_count': len(raw_records) == len(records) == len(decls),
        'fresh_compile': path.stat().st_mtime_ns <= logpath.stat().st_mtime_ns <= exitpath.stat().st_mtime_ns,
    }
    reports.append({
        'file': str(path.relative_to(root)),
        'lines': len(source.splitlines()),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'log_sha256': hashlib.sha256(logpath.read_bytes()).hexdigest(),
        'declarations': len(decls),
        'checks': checks,
        'pass': all(checks.values()),
        'axioms': records,
    })
assembly = {
    'moving_root_exact_append': (base / 'MovingRoot.lean').read_bytes() ==
        (base / 'PolynomialGrid.lean').read_bytes() + (base / 'MovingRootPart.lean.txt').read_bytes(),
    'obstruction_exact_append': (base / 'SeedObstruction.lean').read_bytes() ==
        (base / 'MovingRoot.lean').read_bytes() + (base / 'SeedObstructionPart.lean.txt').read_bytes(),
    'shared_byte_identical': shared.read_bytes() == (base / 'SeedObstruction.lean').read_bytes(),
}
report = {
    'status': 'abstract finite certificate and seed-transport obstruction; actual coupling remains open',
    'goalNeg2_proved': False,
    'round9_coupling_premise_proved': False,
    'actual_polynomial_certificate_proved': False,
    'actual_crossing_jet_nonzero_proved': False,
    'actual_whole_kernel_definiteness_proved': False,
    'distinct_declarations': reports[-1]['declarations'],
    'independently_compiled_files': len(paths),
    'assembly': assembly,
    'files': reports,
    'pass': all(assembly.values()) and all(r['pass'] for r in reports),
}
(base / 'CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))
raise SystemExit(0 if report['pass'] else 1)
