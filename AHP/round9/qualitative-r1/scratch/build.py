#!/usr/bin/env python3
"""Assemble scratch/Abstract1.lean (D1IVT-only test of the abstract part),
Appendix.lean (the round-9 appendix) and a full draft (round-8 Attempt + appendix)."""
import re
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
core = (HERE / 'AbstractCore.lean').read_text() + (HERE / 'AbstractWeak.lean').read_text()
conc = (HERE / 'ConcreteCore.lean').read_text()
weakc = HERE / 'ConcreteWeak.lean'
if weakc.exists():
    conc = conc + weakc.read_text()
abstract_names = re.findall(r'^theorem\s+(\S+)', core, re.M)
# 1. scratch test of the abstract part (imports only the frozen, Mathlib-only D1IVT)
(HERE / 'Abstract1.lean').write_text((HERE / 'scratch_head.lean').read_text() + core +
    '\nend Abstract\nend AdalyFormal.Round9.Guarded.Qualitative\n')
# 2. the appendix
head = (HERE / 'appendix_head.lean').read_text()
tail = '\nend Abstract\n\n' + ''.join(f'#print axioms {n}\n' for n in abstract_names) + \
    '\nend AdalyFormal.Round9.Guarded.Qualitative\n\n'
app = head + core + tail + conc
(ROOT / 'Appendix.lean').write_text(app)
pre = Path('/home/sebastian/BalabanCoercivityLemma/AHP/round8/guarded-idea/Attempt.lean').read_text()
out = sys.argv[1] if len(sys.argv) > 1 else 'Draft1.lean'
(ROOT / out).write_text(pre + app)
print('prefix', len(pre.splitlines()), 'appendix', len(app.splitlines()), '->', out,
      'abstract theorems', len(abstract_names))
