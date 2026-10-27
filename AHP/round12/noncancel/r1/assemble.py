#!/usr/bin/env python3
"""Concatenate compact fragments; imports remain frozen lean/src/DrEquiv only."""
from pathlib import Path
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--publish', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
text = (root / 'StarKernel.lean').read_text()
text += (root / 'PlaquetteAppendix.lean.txt').read_text()
(root / 'Plaquette.lean').write_text(text)
text += (root / 'TraceAppendix.lean.txt').read_text()
(root / 'Trace.lean').write_text(text)
text += (root / 'PathAppendix.lean.txt').read_text()
text += (root / 'GaugeAppendix.lean.txt').read_text()
(root / 'Attempt.lean').write_text(text)
if args.publish:
    shared = root.parents[1] / 'shared' / 'noncancel'
    shared.mkdir(parents=True, exist_ok=True)
    (shared / 'R1_Star.lean').write_text(text)
