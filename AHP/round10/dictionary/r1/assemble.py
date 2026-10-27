#!/usr/bin/env python3
"""Assemble standalone development files, only inside this track."""
from pathlib import Path
root = Path(__file__).resolve().parent
(root / 'Gauge.lean').write_text((root / 'Core.lean').read_text() + '\n' +
                               (root / 'U1Appendix.lean').read_text())

if __import__('sys').argv[1:] == ['final']:
    repo = root.parents[3]
    earlier = (repo / 'AHP/round9/qualitative-r2/Attempt.lean').read_text()
    symm = (repo / 'AHP/round6/closedform-r1/Attempt.lean').read_text()
    start = symm.index('namespace AdalyFormal.Round6.Guarded.ClosedFormR1')
    marker = '#print axioms twoSite_exact_symmetry'
    end = symm.index(marker, start) + len(marker)
    symm = symm[start:end] + '\nend AdalyFormal.Round6.Guarded.ClosedFormR1\n'
    (root / 'Round6Symmetry.lean.txt').write_text(symm)
    gauge = (root / 'Gauge.lean').read_text().removeprefix('import DrEquiv\n')
    translation = (root / 'Translation.lean').read_text().removeprefix('import DrEquiv\n')
    (root / 'Attempt.lean').write_text(earlier + '\n' + gauge + '\n' + translation +
                                      '\n' + symm + '\n' + (root / 'ActualAppendix.lean').read_text())
