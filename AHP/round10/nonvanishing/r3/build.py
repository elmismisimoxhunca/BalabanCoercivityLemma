#!/usr/bin/env python3
"""Assemble short frozen-import harnesses; do not touch byte-identical outputs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def put(name,text):
    p=ROOT/name
    if not p.exists() or p.read_text()!=text:
        p.write_text(text)

base=(ROOT/'Flux.lean').read_text()+(ROOT/'TorusAppendix.lean.txt').read_text()
put('TorusFlux.lean',base)
physical=base.replace('import DrEquiv\n','import DrEquiv\nimport ZXR2Flat6\n',1)+(ROOT/'Coordinates.lean.txt').read_text()+(ROOT/'BlockingAppendix.lean.txt').read_text()
put('PhysicalBlocking.lean',physical)
put('DilatedFlux.lean',physical+(ROOT/'Geometry.lean.txt').read_text()+(ROOT/'DilatedAppendix.lean.txt').read_text())
